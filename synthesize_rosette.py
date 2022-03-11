import subprocess
import pyparsing as pp
import os
import ir
from analysis import CodeInfo
from ir import *
from rosette_translator import toRosette
from smt_util import toSMT
from synthesis_common import generateTypes, verify_synth_result
import process_tracker

import typing
from typing import Any, Callable, Dict, Union, IO


# utils for converting rosette output to IR
def generateAST(expr: str) -> typing.List[Any]:
    s_expr = pp.nestedExpr(opener="(", closer=")")
    parser = pp.ZeroOrMore(s_expr)
    try:
        ast = parser.parseString(expr, parseAll=True).asList()
    except:
        raise Exception(f"Failed to parse Rosette output: {expr}")
    return ast  # type: ignore


def parseOutput(resultSynth: typing.List[str]) -> typing.List[str]:
    output = []
    for i in range(len(resultSynth)):
        s = ""
        if "define" in resultSynth[i]:
            s = resultSynth[i]
            for j in range(i + 1, len(resultSynth)):
                if "/" not in resultSynth[j]:
                    s += resultSynth[j]
                else:
                    i = j + 1
                    break
            output.append(s)
    return output


def toExpr(
    ast: typing.List[Any], fnsType: Dict[Any, Any], varType: Dict[str, Type]
) -> Expr:

    expr_bi: Dict[str, Callable[..., Expr]] = {
        "equal?": Eq,
        "+": Add,
        "-": Sub,
        "*": Mul,
        "<": Lt,
        "<=": Le,
        ">": Gt,
        ">=": Ge,
        "&&": And,
        "or": Or,
        "=>": Implies,
    }
    expr_uni = {"not": Not}
    if isinstance(ast, list):
        if ast[0] == "define":
            return toExpr(ast[2], fnsType, varType)
        elif ast[0] == "choose":
            return toExpr(ast[1], fnsType, varType)
        elif ast[0] in expr_bi.keys():
            return expr_bi[ast[0]](
                *[toExpr(ast[i], fnsType, varType) for i in range(1, len(ast))]
            )
        elif ast[0] in expr_uni.keys():
            return expr_uni[ast[0]](toExpr(ast[1], fnsType, varType))
        elif ast[0] == "if":
            return Ite(
                toExpr(ast[1], fnsType, varType),
                toExpr(ast[2], fnsType, varType),
                toExpr(ast[3], fnsType, varType),
            )
        elif ast[0] == "length":
            return Call("list_length", Int(), toExpr(ast[1], fnsType, varType))
        elif ast[0] == "=":
            return Call(
                "=",
                Bool(),
                toExpr(ast[1], fnsType, varType),
                toExpr(ast[2], fnsType, varType),
            )
        elif ast[0] == "list-append" or ast[0] == "append":
            elem = toExpr(ast[2], fnsType, varType)
            return Call(
                "list_append",
                List(elem.type),
                toExpr(ast[1], fnsType, varType),
                elem,
            )
        elif ast[0] == "list-prepend":
            elem = toExpr(ast[1], fnsType, varType)
            return Call(
                "list_prepend",
                List(elem.type),
                elem,
                toExpr(ast[2], fnsType, varType),
            )
        elif ast[0] == "list-ref-noerr":
            list_expr = toExpr(ast[1], fnsType, varType)
            return Call(
                "list_get",
                list_expr.type.args[0],
                list_expr,
                toExpr(ast[2], fnsType, varType),
            )
        elif ast[0] == "list-tail-noerr":
            list_expr = toExpr(ast[1], fnsType, varType)
            return Call(
                "list_tail",
                list_expr.type,
                list_expr,
                toExpr(ast[2], fnsType, varType),
            )
        elif ast[0] == "list-concat":
            return Call(
                "list_concat",
                List(Int()),
                toExpr(ast[1], fnsType, varType),
                toExpr(ast[2], fnsType, varType),
            )
        elif ast[0] == "list-take-noerr":
            return Call(
                "list_take",
                List(Int()),
                toExpr(ast[1], fnsType, varType),
                toExpr(ast[2], fnsType, varType),
            )
        elif ast[0] == "make-tuple":
            arg_eval = []
            for alen in range(1, len(ast)):
                arg_eval.append(toExpr(ast[alen], fnsType, varType))
            return MakeTuple(*arg_eval)
        elif ast[0] == "tupleGet":
            return TupleGet(
                toExpr(ast[1], fnsType, varType),
                toExpr(ast[2], fnsType, varType),
            )
        elif ast[0] == "set-create":
            return Call(ast[0], Set(Int()))
        elif ast[0] == "set-insert":
            v = toExpr(ast[1], fnsType, varType)
            s1 = toExpr(ast[2], fnsType, varType)
            return Call(ast[0], Set(v.type), v, s1)
        elif ast[0] == "set-singleton":
            v = toExpr(ast[1], fnsType, varType)
            return Call(ast[0], Set(v.type), v)
        elif ast[0] == "set-eq":
            s1 = toExpr(ast[1], fnsType, varType)
            s2 = toExpr(ast[2], fnsType, varType)
            return Eq(s1, s2)
        elif ast[0] == "set-union" or ast[0] == "set-minus":
            s1 = toExpr(ast[1], fnsType, varType)
            s2 = toExpr(ast[2], fnsType, varType)
            return Call(ast[0], s1.type, s1, s2)
        elif ast[0] == "set-subset":
            s1 = toExpr(ast[1], fnsType, varType)
            s2 = toExpr(ast[2], fnsType, varType)
            return Call(ast[0], Bool(), s1, s2)
        elif ast[0] == "set-member":
            v = toExpr(ast[1], fnsType, varType)
            s = toExpr(ast[2], fnsType, varType)
            return Call(ast[0], Bool(), v, s)
        elif ast[0] in fnsType.keys():
            arg_eval = []
            for alen in range(1, len(ast)):
                arg_eval.append(toExpr(ast[alen], fnsType, varType))
            retT = fnsType[ast[0]].args[0]
            return Call(ast[0], retT, *arg_eval)
        else:
            raise Exception(f"Unexpected function name: {ast[0]}")
    else:
        if ast.isnumeric():
            return IntLit(int(ast))
        elif ast == "true":
            return BoolLit(True)
        elif ast == "false":
            return BoolLit(False)
        elif ast in fnsType.keys():
            return Var(ast, fnsType[ast])
        else:
            return Var(ast, varType[ast])


def toSynthesize(
    loopAndPsInfo: typing.List[Union[CodeInfo, Expr]], lang: typing.List[Expr]
) -> typing.List[str]:
    synthNames = []
    for i in loopAndPsInfo:
        if isinstance(i, CodeInfo):
            synthNames.append(i.name)
        else:
            synthNames.append(i.args[0])
    for l in lang:
        if l.args[1] == None:
            synthNames.append(l.args[0])
    return synthNames


def synthesize(
    basename: str,
    targetLang: typing.List[Expr],
    vars: typing.Set[Expr],
    invAndPs: typing.List[Expr],
    preds: typing.List[Expr],
    vc: Expr,
    loopAndPsInfo: typing.List[Union[CodeInfo, Expr]],
    cvcPath: str,
    uid: int = 0,
    noVerify: bool = False,
    unboundedInts: bool = False,
) -> typing.List[Expr]:
    invGuess: typing.List[Any] = []
    synthDir = "./synthesisLogs/"
    if not os.path.exists(synthDir):
        os.mkdir(synthDir)

    while True:
        synthFile = synthDir + basename + f"_{uid}" + ".rkt"

        prev_vc = vc.toSMT()
        new_vars: typing.Set[Expr] = set()
        while True:
            expr_count: Dict[str, int] = {}
            vc.countVariableUses(expr_count)

            vc = vc.optimizeUselessEquality(expr_count, new_vars)

            if vc.toSMT() == prev_vc:
                break  # run to fixpoint
            else:
                prev_vc = vc.toSMT()

        vars = vars.union(new_vars)
        for var in list(vars):
            if var.args[0] not in expr_count:
                vars.remove(var)

        ##### synthesis procedure #####
        toRosette(
            synthFile,
            targetLang,
            vars,
            invAndPs,
            preds,
            vc,
            loopAndPsInfo,
            invGuess,
            unboundedInts,
        )

        synthNames = toSynthesize(loopAndPsInfo, targetLang)
        procSynthesis = subprocess.Popen(
            ["racket", synthFile], stdout=subprocess.PIPE, stderr=subprocess.PIPE
        )
        process_tracker.all_processes.append(procSynthesis)

        try:
            resultSynth = [
                l.decode("utf-8").rstrip("\n")
                for l in typing.cast(IO[bytes], procSynthesis.stdout).readlines()
            ]

            exitCode = procSynthesis.wait()
            if exitCode != 0:
                raise Exception(f"Synthesis failed: exit code {exitCode}")

            ##### End of Synthesis #####

            #####parsing output of rosette synthesis#####
            varTypes = {}
            for i in loopAndPsInfo:
                if isinstance(i, CodeInfo):
                    varTypes[i.name] = generateTypes(
                        i.modifiedVars + i.readVars + list(vars)
                    )
                else:
                    varTypes[i.args[0]] = generateTypes(i.args[2:])
            for l_i in targetLang:
                varTypes[l_i.args[0]] = generateTypes(l_i.args[2:])

            if resultSynth[0] == "#t":
                output = parseOutput(resultSynth[1:])
                candidateDict = {}
                fnsType = generateTypes(targetLang)
                for synthFun in invAndPs:
                    allVars = synthFun.args[2:]
                    ceName = synthFun.args[0]
                    fnsType[ceName] = Fn(
                        synthFun.args[1].type,
                        *[v.type for v in allVars],
                    )
                for n in synthNames:
                    for r in output:
                        if "define (" + n in r:
                            startIndex = r.find("(")
                            candidateDict[n] = toExpr(
                                generateAST(r[startIndex:])[0], fnsType, varTypes[n]
                            )
            else:
                raise Exception("Synthesis failed")
            #####candidateDict --> definitions of all functions to be synthesized#####

            ##### generating function definitions of all the functions to be synthesized#####
            candidatesSMT = []
            for synthFun in invAndPs:
                allVars = synthFun.args[2:]
                ceName = synthFun.args[0]

                if ceName not in candidateDict:
                    # Rosette will not return a function if no choice needs to be made
                    candidateDict[ceName] = synthFun.args[1]

                candidatesSMT.append(
                    FnDecl(
                        ceName,
                        synthFun.args[1].type,
                        candidateDict[ceName],
                        *allVars,
                    )
                )

            ##### verification of synthesized ps/inv
            print("====== verification")

            verifyLogs: typing.List[str] = []

            if noVerify:
                print("Not verifying solution")
                resultVerify = "unsat"
            else:
                resultVerify, verifyLogs = verify_synth_result(
                    basename,
                    targetLang,
                    vars,
                    preds,
                    vc,
                    loopAndPsInfo,
                    cvcPath,
                    synthDir,
                    candidatesSMT,
                    candidateDict,
                    fnsType,
                    uid,
                )

            print("Verification Output:", resultVerify)
            if resultVerify == "unsat":
                print(
                    "Verified PS and INV Candidates ",
                    "\n\n".join([str(c) for c in candidatesSMT]),
                )
                return candidatesSMT
            else:
                print(
                    "verification failed",
                    "\n\n".join([str(c) for c in candidatesSMT]),
                )
                print("\n".join(verifyLogs))
                invGuess.append(resultSynth[1])
                print(invGuess)
                raise Exception("Verification failed")
        finally:
            procSynthesis.terminate()
