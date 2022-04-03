import subprocess
from analysis import CodeInfo
from ir import *
from llvmlite.binding import ValueRef

import typing
from typing import Optional, Dict, Union, Any

from smt_util import toSMT


class SynthesisFailed(Exception):
    pass


class VerificationFailed(Exception):
    pass


def generateTypes(lang: typing.List[Union[Expr, ValueRef]]) -> Dict[str, Type]:
    fnsType = {}

    for l in lang:
        if l.type.name == "Function":
            if not isinstance(l, ValueRef):
                fnsType[l.args[0]] = l.type
            else:
                fnsType[l.name] = parseTypeRef(l.type)
        else:
            if not isinstance(l, ValueRef):
                fnsType[l.args[0]] = l.type
            else:
                fnsType[l.name] = parseTypeRef(l.type)
    return fnsType


def parseCandidates(
    candidate: Union[Expr, str],
    inCalls: typing.List[Any],
    fnsType: Dict[Any, Any],
    fnCalls: typing.List[Any],
    extractedLambdas: typing.List[Expr],
    inFunctionName: str,
) -> Optional[typing.Tuple[typing.List[Any], typing.List[Any]]]:
    if not isinstance(candidate, Expr):
        return inCalls, fnCalls
    else:
        for a in candidate.args:
            parseCandidates(
                a, inCalls, fnsType, fnCalls, extractedLambdas, inFunctionName
            )
        if candidate.kind == Expr.Kind.Call:
            print(candidate)
            if (
                candidate.args[0] in fnsType.keys()
                and candidate.args[0] != inFunctionName
            ):
                fnCalls.append(candidate.args[0])
            new_args = []
            for ar in candidate.args:
                print(ar)
                if not isinstance(ar, str):
                    if ar.type.name == "Function" and ar.args[0] in fnsType.keys():
                        # TODO(shadaj): this logic doesn't correctly handle
                        # multiple function parameters
                        inCalls.append((candidate.args[0], ar.args[0]))
                        new_args.append(ar)
                    elif ar.kind == Expr.Kind.Lambda:
                        lambda_name = f"lambda_{len(extractedLambdas)}"
                        extractedLambdas.append(
                            FnDeclNonRecursive(
                                lambda_name, ar.type.args[0], ar.args[0], *ar.args[1:]
                            )
                        )
                        fnCalls.append(lambda_name)
                        # inCalls.append((candidate.args[0], lambda_name))
                        new_args.append(Var(lambda_name, ar.type))
                    else:
                        new_args.append(ar)
                else:
                    new_args.append(ar)
            candidate.args = new_args
        return inCalls, fnCalls


def verify_synth_result(
    basename: str,
    targetLang: typing.List[Expr],
    vars: typing.Set[Expr],
    preds: Union[str, typing.List[Expr]],
    vc: Expr,
    loopAndPsInfo: typing.List[Union[CodeInfo, Expr]],
    cvcPath: str,
    synthDir: str,
    candidatesSMT: typing.List[Expr],
    candidateDict: Dict[str, Expr],
    fnsType: Dict[str, Type],
    uid: int,
) -> typing.Tuple[str, typing.List[str]]:
    inCalls: typing.List[Any] = []
    fnCalls: typing.List[Any] = []
    extractedLambdas: typing.List[Expr] = []
    for ce in loopAndPsInfo:
        inCalls, fnCalls = parseCandidates(  # type: ignore
            candidateDict[ce.name if isinstance(ce, CodeInfo) else ce.args[0]],
            inCalls,
            fnsType,
            fnCalls,
            extractedLambdas,
            ce.name if isinstance(ce, CodeInfo) else ce.args[0],
        )

    targetLang = targetLang + extractedLambdas

    for langFn in targetLang:
        if langFn.args[1] != None:
            inCalls, fnCalls = parseCandidates(  # type: ignore
                langFn.args[1],
                inCalls,
                fnsType,
                fnCalls,
                extractedLambdas,
                langFn.args[0],
            )

    inCalls, fnCalls = parseCandidates(vc, inCalls, fnsType, fnCalls, extractedLambdas, None)  # type: ignore

    inCalls = list(set(inCalls))
    fnCalls = list(set(fnCalls))

    print(candidateDict)
    print(extractedLambdas)
    print(candidatesSMT)

    verifFile = synthDir + basename + f"_{uid}" + ".smt"
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
