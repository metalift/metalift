import subprocess
import pyparsing as pp
import os
import ir
from analysis import CodeInfo
from ir import (
    Type,
    PrintMode,
    Expr,
    parseTypeRef,
    MLInst_Assert,
    Call,
    FnDecl,
    Bool,
    Not,
    Add,
    Sub,
    Mul,
    Le,
    Lt,
    Ge,
    Gt,
    And,
    Or,
    Implies,
    Eq,
    Int,
    Bool,
    List,
    Ite,
    IntLit,
    Var,
    parseTypeRef,
)
from rosette_translator import toRosette
from llvmlite.binding import ValueRef

import typing
from typing import Any, Callable, Dict, Optional, Set, Union


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
        elif ast[0] in fnsType.keys():
            arg_eval = []
            for alen in range(1, len(ast)):
                arg_eval.append(toExpr(ast[alen], fnsType, varType))
            retT = fnsType[ast[0]]
            return Call(ast[0], retT, *arg_eval)
        else:
            raise Exception(f"Unexpected function name: {ast[0]}")
    else:
        if ast.isnumeric():

            return IntLit(ast)
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

    if isinstance(candidate, str):
        return None
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


def filterArgs(argList: typing.List[Expr]) -> typing.List[Expr]:
    newArgs = []
    for a in argList:
        if a.type.name != "Function":
            newArgs.append(a)
    return newArgs


def filterBody(funDef: Expr, funCall: str, inCall: str) -> Expr:

    if funDef.kind.value in [
        "+",
        "-",
        "*",
        "=",
        "<",
        "=",
        ">=",
        "<=",
        "and",
        "or",
        "=>",
    ]:
        newArgs = [
            filterBody(funDef.args[0], funCall, inCall),
            filterBody(funDef.args[1], funCall, inCall),
        ]
        return Expr(funDef.kind, funDef.type, newArgs)
    elif funDef.kind.value == "not":
        return Not(filterBody(funDef.args[0], funCall, inCall))
    elif funDef.kind.value == "ite":
        return Ite(
            filterBody(funDef.args[0], funCall, inCall),
            filterBody(funDef.args[1], funCall, inCall),
            filterBody(funDef.args[2], funCall, inCall),
        )

    elif funDef.kind.value == "call":

        if funDef.type.name == "Function":
            newArgs = []

            for i in range(1, len(funDef.args)):
                newArgs.append(filterBody(funDef.args[i], funCall, inCall))
            return Call(inCall, funDef.type, *newArgs)

        elif funDef.args[0] == funCall:
            newArgs = []
            for i in range(1, len(funDef.args)):
                if funDef.args[i].type.name != "Function":
                    newArgs.append(filterBody(funDef.args[i], funCall, inCall))
            return Call(funCall + "_" + inCall, funDef.type, *newArgs)
        else:
            newArgs = []
            for i in range(1, len(funDef.args)):
                newArgs.append(filterBody(funDef.args[i], funCall, inCall))
            return Call(funDef.args[0], funDef.type, *newArgs)
    else:
        return funDef


def toSynthesize(
    loopAndPsInfo: typing.List[CodeInfo], lang: typing.List[Expr]
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
    vars: Set[Expr],
    invAndPs: typing.List[Expr],
    preds: typing.List[Expr],
    vc: Expr,
    loopAndPsInfo: typing.List[CodeInfo],
    cvcPath: str,
) -> typing.List[Expr]:
    invGuess: typing.List[Any] = []
    synthDir = "./synthesisLogs/"
    if not os.path.exists(synthDir):
        os.mkdir(synthDir)

    while True:
        synthFile = synthDir + basename + ".rkt"

        ##### synthesis procedure #####
        toRosette(synthFile, lang, vars, invAndPs, preds, vc, loopAndPsInfo, invGuess)

        synthNames = toSynthesize(loopAndPsInfo, lang)
        procSynthesis = subprocess.run(["racket", synthFile], stdout=subprocess.PIPE)
        resultSynth = procSynthesis.stdout.decode("utf-8").split("\n")
        print(resultSynth)
        ##### End of Synthesis #####

        #####parsing output of rosette synthesis#####
        varTypes = {}
        for i in loopAndPsInfo:
            if isinstance(i, CodeInfo):
                varTypes[i.name] = generateTypes(i.modifiedVars + i.readVars)
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
                candidateDict[ce.name], inCalls, fnsType, fnCalls
            )
        inCalls = list(set(inCalls))
        fnCalls = list(set(fnCalls))
        #####fncalls --> functions from the target language used in ps and invariants, incalls --> call sites for inlining#####

        ##### generating function definitions of all the functions to be synthesized#####
        candidatesSMT = []
        for ce in loopAndPsInfo:
            candidatesSMT.append(
                FnDecl(
                    ce.name,
                    ce.retT,
                    candidateDict[ce.name],
                    *ce.modifiedVars,
                    *ce.readVars,
                )
            )
        for l in lang:
            if l.args[1] == "":
                l.args[1] = candidateDict[l.args[0]]

        ##### verification of synthesized ps/inv
        print("====== verification")
        verifFile = synthDir + basename + ".smt"
        ir.printMode = PrintMode.SMT
        toSMT(lang, vars, candidatesSMT, preds, vc, verifFile, inCalls, fnCalls)

        procVerify = subprocess.run(
            [cvcPath, "--lang=smt", "--tlimit=100000", verifFile],
            stdout=subprocess.PIPE,
        )

        if procVerify.returncode < 0:
            resultVerify = "SAT/UNKNOW"
        else:
            procOutput = procVerify.stdout
            resultVerify = procOutput.decode("utf-8").split("\n")[0]

        print("Vefication Output ", resultVerify)
        break
        if resultVerify == "unsat":
            print("Candidates Verified")
            break
        else:
            print("verification failed")
            invGuess.append(resultSynth[1])
            print(invGuess)
            raise Exception()

    return candidatesSMT


def toSMT(
    targetLang: typing.List[Any],
    vars: Set[Expr],
    invAndPs: typing.List[Expr],
    preds: Union[str, typing.List[Any]],
    vc: Expr,
    outFile: str,
    inCalls: typing.List[Any],
    fnCalls: typing.List[Any],
) -> None:
    # order of appearance: inv and ps grammars, vars, non inv and ps preds, vc
    with open(outFile, mode="w") as out:

        out.write(open("./utils/list-axioms.smt", "r").read())

        if inCalls:

            fnDecls = []
            for i in inCalls:
                for t in targetLang:
                    if i[1] == t.args[0]:
                        fnDecls.append(t)

            for i in inCalls:
                for t in targetLang:
                    if i[0] == t.args[0]:
                        # parse body
                        newBody = filterBody(t.args[1], i[0], i[1])

                        # remove function type args
                        newArgs = filterArgs(t.args[2:])
                        fnDecls.append(
                            FnDecl(t.args[0] + "_" + i[1], t.type, newBody, *newArgs)
                        )

            out.write("\n\n".join([str(t) for t in fnDecls]))

            candidates = []

            for cand in invAndPs:
                newBody = cand.args[1]
                for idx, i in enumerate(inCalls):
                    newBody = filterBody(newBody, i[0], i[1])
                candidates.append(
                    FnDecl(cand.args[0], cand.type, newBody, *cand.args[2:])
                )
            out.write("\n\n".join(["\n%s\n" % (cand) for cand in candidates]))
        elif fnCalls:
            out.write(
                "\n\n".join(
                    ["\n%s\n" % (t) if t.args[0] in fnCalls else "" for t in targetLang]
                )
            )
            out.write("\n\n".join(["\n%s\n" % (cand) for cand in invAndPs]))
        else:
            out.write("\n\n".join(["\n%s\n" % (cand) for cand in invAndPs]))

        v = "\n".join(
            ["(declare-const %s %s)" % (v.args[0], v.type) for v in vars]
        )  # name and type
        out.write("\n%s\n\n" % v)

        ##### ToDo write axioms using the construct
        if "count" in outFile:
            out.write(open("./utils/map_reduce_axioms.txt", "r").read())

        if isinstance(preds, str):
            out.write("%s\n\n" % preds)

        # a list of Exprs - print name, args, return type
        elif isinstance(preds, list):
            preds = "\n".join(
                [
                    "(define-fun %s (%s) (%s) )"
                    % (
                        p.args[0],
                        " ".join("(%s %s)" % (a.args[0], a.type) for a in p.args[1:]),
                        p.type,
                    )
                    for p in preds
                ]
            )
            out.write("%s\n\n" % preds)

        else:
            raise Exception("unknown type passed in for preds: %s" % preds)

        out.write("%s\n\n" % MLInst_Assert(Not(vc)))
        out.write("(check-sat)\n(get-model)")
