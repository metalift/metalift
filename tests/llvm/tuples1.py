import os
import sys

from metalift.analysis import CodeInfo, analyze
from metalift.ir import *
from metalift.rosette_translator import toRosette
from metalift.smt_util import toSMT

from metalift.synthesize_auto import synthesize


def tuple_mult(t):
    return Call("tuple_mult", Int(), t)


def grammar(ci: CodeInfo):
    name = ci.name
    if name.startswith("inv"):
        raise Exception("no invariant")
    else:  # ps
        r = ci.modifiedVars[0]
        (x, y) = ci.readVars
        summary = Choose(
            Eq(r, Add(tuple_mult(Tuple(x, x)), tuple_mult(Tuple(y, y)))),
            Eq(r, Sub(tuple_mult(Tuple(x, x)), tuple_mult(Tuple(y, y)))),
        )
        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)


def targetLang():
    x = Var("x", TupleT(Int(), Int()))
    tuple_mult = FnDeclRecursive(
        "tuple_mult", Int(), Mul(TupleGet(x, IntLit(0)), TupleGet(x, IntLit(1))), x
    )
    return [tuple_mult]


if __name__ == "__main__":
    filename = "tests/llvm/tuples1.ll"
    basename = "tuples1"

    fnName = "_Z4testii"
    loopsFile = "tests/llvm/tuples1.loops"

    cvcPath = "cvc5"

    (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile)

    print("====== synthesis")
    invAndPs = [grammar(ci) for ci in loopAndPsInfo]

    lang = targetLang()

    candidates = synthesize(
        basename,
        lang,
        vars,
        invAndPs,
        preds,
        vc,
        loopAndPsInfo,
        cvcPath,
    )

    print("====== verified candidates")
    for c in candidates:
        print(c, "\n")

    # (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile)

    # print("====== synthesis")
    # invAndPs = [grammar(ci) for ci in loopAndPsInfo]

    # lang = targetLang()
    # invGuess: typing.List[Any] = []
    # unboundedInts = False
    # synthDir = "./tests/"
    # synthFile = synthDir + basename + ".rkt"

    # toRosette(
    #     synthFile,
    #     lang,
    #     vars,
    #     invAndPs,
    #     preds,
    #     vc,
    #     loopAndPsInfo,
    #     invGuess,
    #     unboundedInts,
    # )

    # ### SMT
    # print("====== verification")

    # #####identifying call sites for inlining #####
    # inCalls: typing.List[Any] = []
    # fnCalls: typing.List[Any] = []

    # ##### generating function definitions of all the functions to be synthesized#####
    # candidatesSMT = []
    # candidateDict = {}
    # r = Var("i11", Int())
    # x = Var("arg", Int())
    # y = Var("arg1", Int())
    # # pretend that we have run synthesis and insert the result into candidateDict to print
    # candidateDict[fnName] = summary(r, x, y)

    # for ce in loopAndPsInfo:
    #     allVars = (
    #         ce.modifiedVars + ce.readVars if isinstance(ce, CodeInfo) else ce.args[2:]
    #     )
    #     ceName = ce.name if isinstance(ce, CodeInfo) else ce.args[0]
    #     candidatesSMT.append(
    #         FnDecl(
    #             ceName,
    #             ce.retT if isinstance(ce, CodeInfo) else ce.type,
    #             candidateDict[ceName],
    #             *allVars,
    #         )
    #     )

    # verifFile = synthDir + basename + ".smt"

    # toSMT(lang, vars, candidatesSMT, preds, vc, verifFile, inCalls, fnCalls)
