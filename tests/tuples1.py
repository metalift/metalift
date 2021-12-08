import os
import sys

from analysis import CodeInfo, analyze
from ir import *
from rosette_translator import toRosette
from smt_util import toSMT


def tuple_mult(t):
    return Call("tuple_mult", Int(), t)

# postcondition for tuples1.c
def summary(r, x, y):
    return Eq(r, Add(tuple_mult(MakeTuple(x, x)), tuple_mult(MakeTuple(y, y))))

def grammar(ci: CodeInfo):
    name = ci.name
    if name.startswith("inv"):
        raise Exception("no invariant")
    else:  # ps
        r = ci.modifiedVars[0]
        (x, y) = ci.readVars
        return Synth(name, summary(r, x, y), *ci.modifiedVars, *ci.readVars)

def targetLang():
    x = Var("x", Tuple(Int(), Int()))
    tuple_mult = FnDecl("tuple_mult", Int(), Mul(First(x), Second(x)), x)
    return [tuple_mult]


if __name__ == "__main__":
    filename = sys.argv[1]
    basename = os.path.splitext(os.path.basename(filename))[0]

    fnName = sys.argv[2]
    loopsFile = sys.argv[3]

    (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile)
    
    print("====== synthesis")
    invAndPs = [grammar(ci) for ci in loopAndPsInfo]

    lang = targetLang()
    invGuess: typing.List[Any] = []
    unboundedInts = False
    synthDir = "./tests/"
    synthFile = synthDir + basename + ".rkt"

    toRosette(synthFile, lang, vars, invAndPs, preds, vc, loopAndPsInfo, invGuess, unboundedInts)


    ### SMT
    print("====== verification")

    #####identifying call sites for inlining #####
    inCalls: typing.List[Any] = []
    fnCalls: typing.List[Any] = []

    ##### generating function definitions of all the functions to be synthesized#####
    candidatesSMT = []
    candidateDict = {}
    r = Var("tmp11", Int())
    x = Var("arg", Int())
    y = Var("arg1", Int())
    # pretend that we have run synthesis and insert the result into candidateDict to print
    candidateDict[fnName] = summary(r, x, y)

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

    verifFile = synthDir + basename + ".smt"

    toSMT(lang, vars, candidatesSMT, preds, vc, verifFile, inCalls, fnCalls)
