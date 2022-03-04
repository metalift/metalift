from analysis import CodeInfo
import subprocess
import pyparsing as pp
import os

from ir import *
from smt_util import toSMT

import typing
from typing import Any, Callable, Dict, Generator, Union


def flatten(L: typing.List[Any]) -> Generator[str, str, None]:
    for l in L:
        if isinstance(l, list):
            yield "("
            yield from flatten(l)
            yield ")"
        else:
            yield l
    return None


def generateAST(expr: str) -> typing.List[Any]:
    s_expr = pp.nestedExpr(opener="(", closer=")")
    parser = pp.ZeroOrMore(pp.Suppress("(exit)") | s_expr)
    ast = parser.parseString(expr, parseAll=True).asList()
    return ast  # type: ignore


def extractFuns(
    targetLang: typing.List[Expr],
) -> typing.Tuple[typing.List[str], typing.List[Type]]:
    funName, returnType = (
        [],
        [],
    )
    for t in targetLang:
        funName.append(t.args[0])
        returnType.append(t.type)
    return funName, returnType


def generateCandidates(
    invAndPs: typing.List[Expr],
    line: str,
    funName: typing.List[str],
    returnType: typing.List[Type],
) -> typing.Tuple[typing.List[Expr], Dict[str, Expr]]:
    candidates, candidatesExpr = [], {}
    ast = generateAST(line)
    for ce in invAndPs:
        name = ce.args[0]
        for a in ast[0]:
            if name in a:
                args = {}
                for v in ce.args[2:]:
                    if isinstance(v, Expr):
                        args[v.args[0]] = v.type
                    else:
                        args[v.name] = parseTypeRef(v.type)

                candidatesExpr[a[0]] = toExpr(a[1], funName, returnType, args, {})
                if isinstance(a[1], str):
                    candidates.append(FnDecl(ce.args[0], ce.type, a[1], *ce.args[2:]))
                else:
                    candidates.append(
                        FnDecl(
                            ce.args[0],
                            ce.type,
                            "(" + " ".join(list(flatten(a[1]))) + ")",
                            *ce.args[2:],
                        )
                    )
    return candidates, candidatesExpr


def toExpr(
    ast: typing.List[Any],
    funName: typing.List[str],
    returnType: typing.List[Type],
    varType: Dict[str, Type],
    letVars: Dict[str, Expr],
) -> Expr:
    expr_bi: Dict[str, Callable[..., Expr]] = {
        "=": Eq,
        "+": Add,
        "-": Sub,
        "*": Mul,
        "<": Lt,
        "<=": Le,
        ">": Gt,
        ">=": Ge,
        "and": And,
        "or": Or,
        "=>": Implies,
    }
    expr_uni = {"not": Not}
    if isinstance(ast, list):
        if ast[0] in expr_bi.keys():
            return expr_bi[ast[0]](
                toExpr(ast[1], funName, returnType, varType, letVars),
                toExpr(ast[2], funName, returnType, varType, letVars),
            )
        elif ast[0] in expr_uni.keys():
            return expr_uni[ast[0]](
                toExpr(ast[1], funName, returnType, varType, letVars)
            )
        elif ast[0] in funName:
            index = funName.index(ast[0])
            return Call(
                ast[0],
                returnType[index],
                toExpr(ast[1], funName, returnType, varType, letVars),
            )
        elif ast[0] == "let":
            newLetVars = dict(letVars)
            newLetVars[ast[1][0][0]] = toExpr(
                ast[1][0][1], funName, returnType, varType, letVars
            )
            return toExpr(ast[2], funName, returnType, varType, newLetVars)
        elif ast[0] == "ite":
            return Ite(
                toExpr(ast[1], funName, returnType, varType, letVars),
                toExpr(ast[2], funName, returnType, varType, letVars),
                toExpr(ast[3], funName, returnType, varType, letVars),
            )
        elif ast[0].startswith("tuple"):
            if "_get" in ast[0]:
                n = int(ast[0].split("_get")[1])
                return TupleGet(
                    toExpr(ast[1], funName, returnType, varType, letVars),
                    IntLit(n),
                )
            else:
                arg_eval = []
                for alen in range(1, len(ast)):
                    arg_eval.append(
                        toExpr(ast[alen], funName, returnType, varType, letVars)
                    )
                return Call(
                    "tuple%d" % (len(ast) - 1),
                    Tuple(
                        arg_eval[0].type,
                        arg_eval[1].type,
                        *[e.type for e in arg_eval[2:]],
                    ),
                    *arg_eval,
                )
        elif ast[0] == "as" and ast[1] == "set.empty":
            return Call("set-create", Set(Int()))  # TODO(shadaj): parse the type
        elif ast[0] == "set.insert":
            v = toExpr(ast[1], funName, returnType, varType, letVars)
            s1 = toExpr(ast[2], funName, returnType, varType, letVars)
            return Call("set-insert", Set(v.type), v, s1)
        elif ast[0] == "set.singleton":
            v = toExpr(ast[1], funName, returnType, varType, letVars)
            return Call("set-singleton", Set(v.type), v)
        elif ast[0] == "set.eq":
            s1 = toExpr(ast[1], funName, returnType, varType, letVars)
            s2 = toExpr(ast[2], funName, returnType, varType, letVars)
            return Eq(s1, s2)
        elif ast[0] == "set.union" or ast[0] == "set.minus":
            s1 = toExpr(ast[1], funName, returnType, varType, letVars)
            s2 = toExpr(ast[2], funName, returnType, varType, letVars)
            if ast[0] == "set-union":
                return Call("set-union", s1.type, s1, s2)
            else:
                return Call("set-minus", s1.type, s1, s2)
        elif ast[0] == "set.subset":
            s1 = toExpr(ast[1], funName, returnType, varType, letVars)
            s2 = toExpr(ast[2], funName, returnType, varType, letVars)
            return Call("set-subset", Bool(), s1, s2)
        elif ast[0] == "set.member":
            v = toExpr(ast[1], funName, returnType, varType, letVars)
            s = toExpr(ast[2], funName, returnType, varType, letVars)
            return Call("set-member", Bool(), v, s)
        else:
            raise Exception("Unknown expression: " + repr(ast))
    else:
        if ast.isnumeric():
            return IntLit(int(ast))
        elif ast == "false":
            return BoolLit(False)
        elif ast == "true":
            return BoolLit(True)
        elif ast in letVars:
            return letVars[ast]
        else:
            return Var(ast, varType[ast])


def synthesize(
    basename: str,
    targetLang: typing.List[Expr],
    vars: typing.Set[Expr],
    invAndPs: typing.List[Expr],
    preds: Union[str, typing.List[Expr]],
    vc: Expr,
    loopAndPsInfo: typing.List[Union[CodeInfo, Expr]],
    cvcPath: str,
    noVerify: bool = False,  # currently ignored
    unboundedInts: bool = False,  # currently ignored
) -> typing.List[Expr]:
    synthDir = "./synthesisLogs/"
    if not os.path.exists(synthDir):
        os.mkdir(synthDir)
    sygusFile = synthDir + basename + ".sl"

    # Generate sygus file for synthesis
    toSMT(
        targetLang,
        vars,
        invAndPs,
        preds,
        vc,
        sygusFile,
        [],
        [f.args[0] for f in targetLang],
        True,
    )

    logfile = synthDir + basename + "_logs.txt"
    synthLogs = open(logfile, "w")
    # Run synthesis subprocess
    proc = subprocess.Popen(
        [cvcPath, "--lang=sygus2", "--output=sygus", "--no-sygus-pbe", sygusFile],
        stdout=synthLogs,
    )

    try:
        funName, returnType = extractFuns(targetLang)
        logfileVerif = open(logfile, "r")
        while True:
            line = logfileVerif.readline()
            if "fail" in line:
                break
            elif "sygus-candidate" in line:
                print("Current PS and INV Guess ", line)
                candidates, _ = generateCandidates(invAndPs, line, funName, returnType)
                smtFile = synthDir + basename + ".smt"
                toSMT(targetLang, vars, candidates, preds, vc, smtFile, [], [], False)

                # run external verification subprocess
                procVerify = subprocess.Popen(
                    [cvcPath, "--lang=smt", "--fmf-fun", "--tlimit=10000", smtFile],
                    stdout=subprocess.PIPE,
                    stderr=subprocess.DEVNULL,
                )
                output = procVerify.stdout.readline()  # type: ignore
                output = output.decode("utf-8")
                if output.count("unsat") == 1:
                    print("UNSAT\n")
                    print(
                        "Verified PS and INV Candidates ",
                        "\n\n".join([str(c) for c in candidates]),
                    )

                    return candidates
                else:
                    print("CVC4 verification Result for Current Guess")
                    print("SAT\n")
            else:
                if proc.poll() is not None:
                    break

        raise Exception("SyGuS failed")
    finally:
        proc.kill()
