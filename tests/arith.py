import os
import sys

from analysis import CodeInfo, analyze
from ir import *

if False:
    from synthesize_rosette import synthesize
else:
    from synthesize_cvc5 import synthesize


def grammar(ci: CodeInfo):
    name = ci.name

    if name.startswith("inv"):
        raise Exception("no invariant")
    else:  # ps
        
        outputVar = ci.modifiedVars[0]
        intLit = Choose(IntLit(0), IntLit(1), IntLit(2), IntLit(3))
        cond = Eq(Choose(*ci.readVars), intLit)
        add_tree = Choose(*ci.readVars)
        for i in range(5):
          add_tree = Choose(add_tree, Add(add_tree, add_tree))
        nested_conditional = IntLit(0)
        for i in range(5):
          nested_conditional = Choose(nested_conditional, Ite(cond, add_tree, nested_conditional))

        summary = Eq(outputVar, nested_conditional)
        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)


def targetLang():
    return []


if __name__ == "__main__":
    filename = "tests/arith.ll"
    basename = "arith"

    fnName = "test"
    loopsFile = "tests/arith.loops"
    cvcPath = "cvc5"

    (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile)
    # print("hi")
    # print(vc)

    print("====== synthesis")
    invAndPs = [grammar(ci) for ci in loopAndPsInfo]

    lang = targetLang()
    candidates = synthesize(
        basename, lang, vars, invAndPs, preds, vc, loopAndPsInfo, cvcPath
    )
    for c in candidates:
        print(c, "\n")
