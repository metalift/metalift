import os
import sys

from analysis import CodeInfo, analyze
from ir import *

if os.environ.get("SYNTH_CVC5") == "1":
    from synthesize_cvc5 import synthesize
else:
    from synthesize_rosette import synthesize


def grammar(ci: CodeInfo):
    name = ci.name

    if name.startswith("inv"):
        raise Exception("no invariant")
    else:  # ps

        outputVar = ci.modifiedVars[0]
        intLit = Choose(IntLit(1), IntLit(2), IntLit(3), IntLit(10))
        cond = Choose(
            Eq(*ci.readVars, intLit), Gt(*ci.readVars, intLit), Le(*ci.readVars, intLit)
        )
        ite = Ite(cond, intLit, intLit)
        summary = Eq(outputVar, ite)
        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)


def targetLang():
    return []


if __name__ == "__main__":
    filename = "tests/ite1.ll"
    basename = "ite1"

    fnName = "test"
    loopsFile = "tests/ite1.loops"
    cvcPath = "cvc5"

    (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile)

    print("====== synthesis")
    invAndPs = [grammar(ci) for ci in loopAndPsInfo]

    lang = targetLang()
    candidates = synthesize(
        basename, lang, vars, invAndPs, preds, vc, loopAndPsInfo, cvcPath
    )
    for c in candidates:
        print(c, "\n")
