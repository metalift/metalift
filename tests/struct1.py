import os
import sys

from metalift.analysis import CodeInfo, analyze
from metalift.ir import *
from metalift.rosette_translator import toRosette
from metalift.smt_util import toSMT


# postcondition for struct1.c
def summary(r, x, y):
    return Eq(r, Call("my_add", Int(), x, y))


def grammar(ci: CodeInfo):
    name = ci.name
    if name.startswith("inv"):
        raise Exception("no invariant")
    else:  # ps
        r = ci.modifiedVars[0]
        (x, y) = ci.readVars
        return Synth(name, summary(r, x, y), *ci.modifiedVars, *ci.readVars)


def targetLang():
    x = Var("x", Int())
    y = Var("y", Int())
    my_add = FnDeclRecursive("my_add", Int(), Add(x, y), x, y)
    return [my_add]


if __name__ == "__main__":
    filename = "tests/struct1.ll"
    basename = "struct1"

    fnName = "test"
    loopsFile = "tests/struct1.loops"

    cvcPath = ""

    (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile)

    print("====== synthesis")
    invAndPs = [grammar(ci) for ci in loopAndPsInfo]

    lang = targetLang()
    invGuess: typing.List[Any] = []
    unboundedInts = False
    synthDir = "./tests/"
    synthFile = synthDir + basename + ".rkt"

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
        listBound=2
    )

    ### SMT
    print("====== verification")

    #####identifying call sites for inlining #####
    inCalls: typing.List[Any] = []
    fnCalls: typing.List[Any] = []

    ##### generating function definitions of all the functions to be synthesized#####
    candidatesSMT = []
    candidateDict = {}
    r = Var("i8", Int())
    x = Var("arg", Int())
    y = Var("arg1", Int())
    # pretend that we have run synthesis and insert the result into candidateDict to print
    candidateDict[fnName] = summary(r, x, y)

    for ce in loopAndPsInfo:
        allVars = (
            ce.modifiedVars + ce.readVars if isinstance(ce, CodeInfo) else ce.args[2:]
        )
        ceName = ce.name if isinstance(ce, CodeInfo) else ce.args[0]
        candidatesSMT.append(
            FnDeclRecursive(
                ceName,
                ce.retT if isinstance(ce, CodeInfo) else ce.type,
                candidateDict[ceName],
                *allVars,
            )
        )

    verifFile = synthDir + basename + ".smt"

    toSMT(lang, vars, candidatesSMT, preds, vc, verifFile, inCalls, fnCalls)
