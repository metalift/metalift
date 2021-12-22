import subprocess
import pyparsing as pp
import os
import ir
from analysis import CodeInfo
from ir import *
from rosette_translator import toRosette
from smt_util import toSMT
from llvmlite.binding import ValueRef

import typing
from typing import Any, Callable, Dict, Optional, Union


# utils for converting rosette output to IR
def generateAST(expr: str) -> typing.List[Any]:
    s_expr = pp.nestedExpr(opener="(", closer=")")
    parser = pp.ZeroOrMore(s_expr)
    ast = parser.parseString(expr, parseAll=True).asList()
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
                toExpr(ast[1], fnsType, varType), toExpr(ast[2], fnsType, varType)
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
            return Call(
                "list_append",
                List(Int()),
                toExpr(ast[1], fnsType, varType),
                toExpr(ast[2], fnsType, varType),
            )
        elif ast[0] == "list-tail-noerr":
            return Call(
                "list_tail",
                List(Int()),
                toExpr(ast[1], fnsType, varType),
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
            retT = [Int() for i in range(len(ast[1]))]
            arg_eval = []
            for alen in range(1, len(ast)):
                arg_eval.append(toExpr(ast[alen], fnsType, varType))
            return Call("tuple%d" % (len(ast) - 1), Tuple(arg_eval[0], arg_eval[1], *arg_eval[2:]), *arg_eval)  # type: ignore
        elif ast[0] == "tupleGet":
            foo = toExpr(ast[2], fnsType, varType)
            return TupleGet(
                toExpr(ast[1], fnsType, varType),
                toExpr(ast[2], fnsType, varType),
            )
        elif ast[0] in fnsType.keys():
            arg_eval = []
            for alen in range(1, len(ast)):
                arg_eval.append(toExpr(ast[alen], fnsType, varType))
            retT = fnsType[ast[0]]
            return Call(ast[0], retT, *arg_eval)  # type: ignore
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
            retT = fnsType[ast]
            return Call(ast, retT)
        else:
            return Var(ast, varType[ast])


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
) -> Optional[typing.Tuple[typing.List[Any], typing.List[Any]]]:
    if isinstance(candidate, str) or candidate.kind == Expr.Kind.Lit:
        return inCalls, fnCalls
    else:
        if candidate.kind.value == "call":
            if candidate.args[0] in fnsType.keys():
                fnCalls.append(candidate.args[0])
            for ar in candidate.args:
                if not isinstance(ar, str):
                    if ar.type.name == "Function":
                        inCalls.append((candidate.args[0], ar.args[0]))
        for a in candidate.args:
            parseCandidates(a, inCalls, fnsType, fnCalls)
        return inCalls, fnCalls


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
        if l.args[1] == "":
            synthNames.append(l.args[0])
    return synthNames


def synthesize(
    basename: str,
    lang: typing.List[Expr],
    vars: typing.Set[Expr],
    invAndPs: typing.List[Expr],
    preds: typing.List[Expr],
    vc: Expr,
    loopAndPsInfo: typing.List[Union[CodeInfo, Expr]],
    cvcPath: str,
    noVerify: bool = False,
    unboundedInts: bool = False,
) -> typing.List[Expr]:
    invGuess: typing.List[Any] = []
    synthDir = "./synthesisLogs/"
    if not os.path.exists(synthDir):
        os.mkdir(synthDir)

    while True:
        synthFile = synthDir + basename + ".rkt"

        ##### synthesis procedure #####
        toRosette(
            synthFile,
            lang,
            vars,
            invAndPs,
            preds,
            vc,
            loopAndPsInfo,
            invGuess,
            unboundedInts,
        )

        synthNames = toSynthesize(loopAndPsInfo, lang)
        procSynthesis = subprocess.run(["racket", synthFile], stdout=subprocess.PIPE)
        resultSynth = procSynthesis.stdout.decode("utf-8").split("\n")
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
        for l_i in lang:
            varTypes[l_i.args[0]] = generateTypes(l_i.args[2:])

        if resultSynth[0] == "#t":
            output = parseOutput(resultSynth[1:])
            candidateDict = {}
            fnsType = generateTypes(lang)
            for n in synthNames:
                for r in output:
                    if "define (" + n in r:
                        candidateDict[n] = toExpr(
                            generateAST(r[1:])[0], fnsType, varTypes[n]
                        )
        else:
            raise Exception("Synthesis failed")
        #####candidateDict --> definitions of all functions to be synthesized#####

        #####identifying call sites for inlining #####
        inCalls: typing.List[Any] = []
        fnCalls: typing.List[Any] = []
        for ce in loopAndPsInfo:
            inCalls, fnCalls = parseCandidates(  # type: ignore
                candidateDict[ce.name if isinstance(ce, CodeInfo) else ce.args[0]],
                inCalls,
                fnsType,
                fnCalls,
            )
        inCalls = list(set(inCalls))
        fnCalls = list(set(fnCalls))
        #####fncalls --> functions from the target language used in ps and invariants, incalls --> call sites for inlining#####

        ##### generating function definitions of all the functions to be synthesized#####
        candidatesSMT = []
        for ce in loopAndPsInfo:
            allVars = (
                ce.modifiedVars + ce.readVars
                if isinstance(ce, CodeInfo)
                else ce.args[2:]
            )
            ceName = ce.name if isinstance(ce, CodeInfo) else ce.args[0]
            candidatesSMT.append(
                FnDecl(
                    ceName,
                    ce.retT if isinstance(ce, CodeInfo) else ce.type,
                    candidateDict[ceName],
                    *allVars,
                )
            )

        ##### verification of synthesized ps/inv
        print("====== verification")
        verifFile = synthDir + basename + ".smt"
        ir.printMode = PrintMode.SMT
        toSMT(lang, vars, candidatesSMT, preds, vc, verifFile, inCalls, fnCalls)

        if noVerify:
            print("Not verifying solution")
            resultVerify = "unsat"
        else:
            procVerify = subprocess.run(
                [cvcPath, "--lang=smt", "--tlimit=100000", verifFile],
                stdout=subprocess.PIPE,
            )

            if procVerify.returncode < 0:
                resultVerify = "SAT/UNKNOWN"
            else:
                procOutput = procVerify.stdout
                resultVerify = procOutput.decode("utf-8").split("\n")[0]

        print("Vefication Output:", resultVerify)
        if resultVerify == "unsat":
            print(
                "Verified PS and INV Candidates ",
                "\n\n".join([str(c) for c in candidatesSMT]),
            )
            break
        else:
            print("verification failed")
            invGuess.append(resultSynth[1])
            print(invGuess)
            raise Exception()

    return candidatesSMT
