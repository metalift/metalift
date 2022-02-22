import os
import sys

from analysis import CodeInfo, analyze
from ir import *
from rosette_translator import toRosette
from smt_util import toSMT
from synthesize_rosette import synthesize


def tuple_add(t):
    return Call("tuple_add", Int(), t)


def grammar(ci: CodeInfo):
    name = ci.name
    if name.startswith("inv"):
        raise Exception("no invariant")
    else:  # ps
        r = ci.modifiedVars[0]
        (x, y) = ci.readVars
        summary = Choose(
            Eq(r, Add(tuple_add(MakeTuple(x, x)), tuple_add(MakeTuple(y, y)))),
            Eq(r, Sub(tuple_add(MakeTuple(x, x)), tuple_add(MakeTuple(y, y)))),
        )
        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)


def targetLang():
    x = Var("x", Tuple(Int(), Int()))
    tuple_add = FnDecl(
        "tuple_add", Int(), Add(TupleGet(x, IntLit(0)), TupleGet(x, IntLit(1))), x
    )
    return [tuple_add]


if __name__ == "__main__":
    filename = "tests/tuples2.ll"
    basename = "tuples2"

    fnName = "_Z4testii"
    loopsFile = "tests/tuples2.loops"
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
        noVerify=False,
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
