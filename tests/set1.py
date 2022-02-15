import os
import sys

from analysis import CodeInfo, analyze
from ir import (
    Choose,
    Eq,
    Synth,
    Call,
    Int,
    IntLit,
    Ite,
    Set,
    Var,
)

if True:
    from synthesize_rosette import synthesize
else:
    from synthesize_cvc5 import synthesize


def grammar(ci: CodeInfo):
    name = ci.name

    if name.startswith("inv"):
        raise Exception("no invariant")
    else:  # ps
        inputS = ci.readVars[0]
        inputAdd = ci.readVars[1]
        inputValue = ci.readVars[2]
        outputVar = ci.modifiedVars[0]

        emptySet = Call("set-create", Set(Int()))

        intLit = Choose(IntLit(0), IntLit(1), IntLit(2), IntLit(3))
        intValue = Choose(inputValue, intLit)

        condition = Eq(inputAdd, intLit)

        setIn = Choose(inputS, emptySet, Call("set-singleton", Set(Int()), intValue))

        setTransform = Choose(
            setIn,
            Call("set-union", Set(Int()), setIn, setIn),
            Call("set-minus", Set(Int()), setIn, setIn),
        )

        chosenTransform = Ite(condition, setTransform, setTransform)

        summary = Eq(outputVar, chosenTransform)
        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)


def targetLang():
    return []


if __name__ == "__main__":
    filename = "tests/set1.ll"
    basename = "set1"

    fnName = "test"
    loopsFile = "tests/set1.loops"
    cvcPath = "cvc5"

    (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile)

    print("====== synthesis")
    invAndPs = [grammar(ci) for ci in loopAndPsInfo]

    lang = targetLang()

    candidates = synthesize(
        basename, lang, vars, invAndPs, preds, vc, loopAndPsInfo, cvcPath
    )
