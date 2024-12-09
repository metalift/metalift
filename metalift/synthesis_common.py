import subprocess
import typing
from typing import Any, Dict, Optional, Union

from llvmlite.binding import ValueRef

from metalift.analysis import CodeInfo
from metalift.ir import *
from metalift.rosette_translator import to_rosette
from metalift.smt_util import toSMT
from tests.python.utils.utils import codegen


class SynthesisFailed(Exception):
    pass


class VerificationFailed(Exception):
    pass


def prune_fn_decls(all_fns: Dict[str, Union[FnDecl, FnDeclRecursive]]) -> FnDecl:
    """
    We process any ite expressions where the condition is a simple boolean.
    This is mostly to simplify reading.
    """

    def prune_ite(expr: Expr) -> Expr:
        if (
            (not isinstance(expr, Expr))
            or isinstance(expr, Var)
            or isinstance(expr, Lit)
        ):
            return expr
        if isinstance(expr, Ite):
            cond = expr.c().map_args(prune_ite)
            if Expr.__eq__(cond, Bool(True).src):
                return expr.e1().map_args(prune_ite)
            elif Expr.__eq__(cond, Bool(False).src):
                return expr.e2().map_args(prune_ite)
            elif isinstance(cond, Call):
                fn_name = cond.name()
                if fn_name in all_fns.keys():
                    fn_body = all_fns[fn_name].body()
                    if Expr.__eq__(fn_body, Bool(True).src):
                        return expr.e1().map_args(prune_ite)
                    elif Expr.__eq__(fn_body, Bool(False).src):
                        return expr.e2().map_args(prune_ite)
            return expr.map_args(prune_ite)
        return expr.map_args(prune_ite)

    new_fns: Dict[str, Union[FnDecl, FnDeclRecursive]] = {}
    for fn_name, fn in all_fns.items():
        new_fns[fn_name] = fn.map_args(prune_ite)
    return new_fns


def get_used_fn_names(synthesized_fn_decls: list[FnDecl | FnDeclRecursive]) -> set[str]:
    """Given all synthesized functions, return a set of DSL function names used in these function definitions."""

    def get_fn_names(expr: Expr | Any, fn_names: set[str]) -> Expr:
        if not isinstance(expr, Expr):
            return expr
        if isinstance(expr, Call):
            fn_names.add(expr.name())
        return expr.map_args(lambda expr: get_fn_names(expr, fn_names))

    fn_names: set[str] = set()
    for fn_decl in synthesized_fn_decls:
        fn_decl.map_args(lambda expr: get_fn_names(expr, fn_names))
    return fn_names


def generate_types(lang: typing.Sequence[Union[Expr, ValueRef]]) -> Dict[str, ObjectT]:
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
                if isinstance(l, Object):
                    fnsType[l.src.args[0]] = l.type
                else:
                    fnsType[l.args[0]] = l.type
            else:
                fnsType[l.name] = parse_type_ref_to_obj(l.type)
    return fnsType


def parse_candidates(
    candidate: Union[Expr, str],
    in_calls: typing.List[Any],
    fns_type: Dict[Any, Any],
    fn_calls: typing.List[Any],
    extracted_lambdas: typing.List[FnDecl],
    in_function_name: str,
) -> tuple[Union[Expr, str], Optional[tuple[typing.List[Any], typing.List[Any]]]]:
    if not isinstance(candidate, Expr):
        return candidate, (in_calls, fn_calls)
    else:
        candidate = candidate.map_args(
            lambda a: parse_candidates(  # type: ignore
                a, in_calls, fns_type, fn_calls, extracted_lambdas, in_function_name
            )[0]
        )
        # if candidate.kind == Expr.Kind.Call:
        if isinstance(candidate, Call):
            if (
                candidate.args[0] in fns_type.keys()
                and candidate.args[0] != in_function_name
            ):
                fn_calls.append(candidate.args[0])

            new_args = []
            for ar in candidate.args:
                if not isinstance(ar, str):
                    # TODO: fix when decided if function will be IR Objects
                    if is_fn_decl_type(ar.type) and ar.args[0] in fns_type.keys():
                        # TODO: this logic doesn't correctly handle
                        # multiple function parameters
                        in_calls.append((candidate.args[0], ar.args[0]))
                        new_args.append(ar)
                    # elif ar.kind == Expr.Kind.Lambda:
                    elif isinstance(ar, Lambda):
                        lambda_name = f"lambda_{len(extracted_lambdas)}"
                        extracted_lambdas.append(
                            FnDecl(
                                # TODO: ar.type no longer has args, find proper substitution
                                lambda_name,
                                ar.type.args[0],  # type: ignore
                                ar.args[0],
                                *ar.args[1:],
                            )
                        )
                        fn_calls.append(lambda_name)
                        in_calls.append((candidate.args[0], lambda_name))
                        new_args.append(Var(lambda_name, ar.type))
                    else:
                        new_args.append(ar)
                else:
                    new_args.append(ar)
            # candidate = Expr(candidate.kind, candidate.type, new_args)
            candidate = Call(new_args[0], candidate.type, *new_args[1:])
        return candidate, (in_calls, fn_calls)


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
    fnsType: Dict[str, ObjectT],
    uid: int,
    use_rosette: bool = False,
) -> tuple[str, typing.List[str]]:
    if use_rosette:
        verifFile = synthDir + basename + f"_{uid}_verif" + ".rkt"
    else:
        verifFile = synthDir + basename + f"_{uid}" + ".smt"
    if use_rosette:
        to_rosette(
            verifFile,
            targetLang,
            vars,
            candidatesSMT,
            preds,  # type: ignore
            vc,
            [],
            [],
            True,
            list_bound=4,  # TODO: bench to find what this value should be
            verify_mode=True,
        )
    else:
        inCalls: typing.List[Any] = []
        fnCalls: typing.List[Any] = []
        extractedLambdas: typing.List[FnDecl] = []
        for ce in loopAndPsInfo:
            updated, (inCalls, fnCalls) = parse_candidates(  # type: ignore
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
                updated, (inCalls, fnCalls) = parse_candidates(  # type: ignore
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
                    # TODO: check
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

        vc, (inCalls, fnCalls) = parse_candidates(vc, inCalls, fnsType, fnCalls, extractedLambdas, None)  # type: ignore

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
        print("Synthesized PS and INV Candidates\n")
        for candidate in candidatesSMT:
            print(
                f"def {candidate.name()}({' '.join([a.args[0] for a in candidate.arguments()])})"
            )
            body = candidate.body()
            if isinstance(body, str):
                print(body)
            else:
                print(codegen(body))
            print("\n\n")

    if use_rosette:
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
                "--tlimit=1",
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
