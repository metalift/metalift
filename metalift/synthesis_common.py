import subprocess
from metalift.analysis import CodeInfo
from metalift.ir import *
from llvmlite.binding import ValueRef

import typing
from typing import Optional, Dict, Union, Any
from metalift.rosette_translator import toRosette

from metalift.smt_util import toSMT


class SynthesisFailed(Exception):
    pass


class VerificationFailed(Exception):
    pass


def generateTypes(lang: typing.Sequence[Union[Expr, ValueRef]]) -> Dict[str, Type]:
    fnsType = {}

    for l in lang:
        # TODO: fix when decided if function will be IR Objects
        if hasattr(l.type, "name") and l.type.name == "Function":
            if not isinstance(l, ValueRef):
                fnsType[l.args[0]] = l.type
            else:
                fnsType[l.name] = parse_type_ref_to_obj(l.type)
        else:
            if not isinstance(l, ValueRef):
                if isinstance(l, NewObject):
                    fnsType[l.src.args[0]] = l.type
                else:
                    fnsType[l.args[0]] = l.type
            else:
                fnsType[l.name] = parse_type_ref_to_obj(l.type)
    return fnsType


def parseCandidates(
    candidate: Union[Expr, str],
    inCalls: typing.List[Any],
    fnsType: Dict[Any, Any],
    fnCalls: typing.List[Any],
    extractedLambdas: typing.List[FnDecl],
    inFunctionName: str,
) -> typing.Tuple[
    Union[Expr, str], Optional[typing.Tuple[typing.List[Any], typing.List[Any]]]
]:
    if not isinstance(candidate, Expr):
        return candidate, (inCalls, fnCalls)
    else:
        candidate = candidate.mapArgs(
            lambda a: parseCandidates(  # type: ignore
                a, inCalls, fnsType, fnCalls, extractedLambdas, inFunctionName
            )[0]
        )
        # if candidate.kind == Expr.Kind.Call:
        if isinstance(candidate, Call):
            if (
                candidate.args[0] in fnsType.keys()
                and candidate.args[0] != inFunctionName
            ):
                fnCalls.append(candidate.args[0])

            new_args = []
            for ar in candidate.args:
                if not isinstance(ar, str):
                    # TODO: fix when decided if function will be IR Objects
                    if (
                        hasattr(ar.type, "name")
                        and ar.type.name == "Function"
                        and ar.args[0] in fnsType.keys()
                    ):
                        # TODO(shadaj): this logic doesn't correctly handle
                        # multiple function parameters
                        inCalls.append((candidate.args[0], ar.args[0]))
                        new_args.append(ar)
                    # elif ar.kind == Expr.Kind.Lambda:
                    elif isinstance(ar, Lambda):
                        lambda_name = f"lambda_{len(extractedLambdas)}"
                        extractedLambdas.append(
                            FnDecl(
                                lambda_name, ar.type.args[0], ar.args[0], *ar.args[1:]
                            )
                        )
                        fnCalls.append(lambda_name)
                        inCalls.append((candidate.args[0], lambda_name))
                        new_args.append(Var(lambda_name, ar.type))
                    else:
                        new_args.append(ar)
                else:
                    new_args.append(ar)
            # candidate = Expr(candidate.kind, candidate.type, new_args)
            candidate = Call(new_args[0], candidate.type, *new_args[1:])
        return candidate, (inCalls, fnCalls)


def verify_synth_result(
    basename: str,
    targetLang: typing.Sequence[Union[FnDeclRecursive, FnDecl, Axiom]],
    vars: typing.Set[Var],
    preds: Union[str, typing.List[Expr]],
    vc: Expr,
    loopAndPsInfo: typing.Sequence[Union[CodeInfo, Expr]],
    cvcPath: str,
    synthDir: str,
    candidatesSMT: typing.List[FnDeclRecursive],
    candidateDict: Dict[str, Expr],
    fnsType: Dict[str, Type],
    uid: int,
    useRosette: bool = False,
) -> typing.Tuple[str, typing.List[str]]:
    if useRosette:
        verifFile = synthDir + basename + f"_{uid}_verif" + ".rkt"
    else:
        verifFile = synthDir + basename + f"_{uid}" + ".smt"

    if useRosette:
        toRosette(
            verifFile,
            targetLang,
            vars,
            candidatesSMT,
            preds,  # type: ignore
            vc,
            [],
            [],
            True,
            listBound=4,  # TODO(shadaj): bench to find what this value should be
            verifyMode=True,
        )
    else:
        inCalls: typing.List[Any] = []
        fnCalls: typing.List[Any] = []
        extractedLambdas: typing.List[FnDecl] = []
        for ce in loopAndPsInfo:
            updated, (inCalls, fnCalls) = parseCandidates(  # type: ignore
                candidateDict[ce.name if isinstance(ce, CodeInfo) else ce.args[0]],
                inCalls,
                fnsType,
                fnCalls,
                extractedLambdas,
                ce.name if isinstance(ce, CodeInfo) else ce.args[0],
            )

            candidateDict[ce.name if isinstance(ce, CodeInfo) else ce.args[0]] = updated  # type: ignore

        targetLang = [*targetLang, *extractedLambdas]

        transformedLang: typing.List[Union[FnDeclRecursive, FnDecl, Axiom]] = []
        for langFn in targetLang:
            if langFn.args[1] is not None:
                # Things are good here
                updated, (inCalls, fnCalls) = parseCandidates(  # type: ignore
                    langFn.args[1],
                    inCalls,
                    fnsType,
                    fnCalls,
                    extractedLambdas,
                    langFn.args[0],
                )
                # Things are good here
                if isinstance(langFn, FnDeclRecursive) or isinstance(langFn, FnDecl):
                    decl: Union[FnDeclRecursive, FnDecl, Axiom] = FnDeclRecursive(
                        langFn.args[0], langFn.returnT(), updated, *langFn.args[2:]
                    )
                elif isinstance(langFn, Axiom):
                    # TODO(shadaj): check
                    decl = Axiom(
                        langFn.args[0], typing.cast(Expr, updated), *langFn.args[2:]
                    )
                else:
                    raise Exception(
                        f"langFn should be either FnDecl or Axiom but not: {langFn})"
                    )
                transformedLang.append(
                    # Expr(
                    #     langFn.kind,
                    #     langFn.type,
                    #     [langFn.args[0], updated, *langFn.args[2:]],
                    # )
                    decl
                )
            else:
                transformedLang.append(langFn)
        targetLang = transformedLang

        vc, (inCalls, fnCalls) = parseCandidates(vc, inCalls, fnsType, fnCalls, extractedLambdas, None)  # type: ignore

        inCalls = list(set(inCalls))
        fnCalls = list(set(fnCalls))

        toSMT(
            targetLang,
            vars,
            candidatesSMT,
            preds,
            vc,
            verifFile,
            inCalls,
            fnCalls,
            False,
        )

    if useRosette:
        procVerify = subprocess.run(
            ["racket", verifFile], stdout=subprocess.PIPE, stderr=subprocess.PIPE
        )

        procOutput = procVerify.stdout
        if procOutput.decode("utf-8").split("\n")[0] == "(unsat)":
            return "unsat", []
        else:
            return "SAT/UNKNOWN", []
    else:
        # run external verification subprocess
        procVerify = subprocess.run(
            [
                cvcPath,
                "--lang=smt",
                "--produce-models",
                "--tlimit=100000",
                verifFile,
            ],
            stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL,
        )

        if procVerify.returncode < 0:
            resultVerify = "SAT/UNKNOWN"
        else:
            procOutput = procVerify.stdout
            resultVerify = procOutput.decode("utf-8").split("\n")[0]
        verifyLogs = procVerify.stdout.decode("utf-8").split("\n")
        return resultVerify, verifyLogs
