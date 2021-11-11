import os
import sys

from analysis import CodeInfo, analyze
from ir import (
    Choose,
    And,
    Or,
    Not,
    Gt,
    Ge,
    Eq,
    Le,
    Le,
    Sub,
    Synth,
    Call,
    Int,
    IntLit,
    BoolLit,
    FnDecl,
    Var,
    Add,
    Implies,
    Ite,
    Set,
)

if False:
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

        emptySet = Call("as emptyset (Set Int)", Set(Int()))

        intLit = Choose(IntLit(0), IntLit(1), IntLit(2), IntLit(3))
        intValue = Choose(inputValue, intLit)

        condition = Eq(inputAdd, intLit)

        setIn = Choose(inputS, emptySet, Call("singleton", Set(Int()), intValue))

        setTransform = Choose(
            setIn,
            Call("union", Set(Int()), setIn, setIn),
            Call("setminus", Set(Int()), setIn, setIn),
        )

        chosenTransform = Ite(condition, setTransform, setTransform)

        summary = Eq(outputVar, chosenTransform)
        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)


def targetLang():
    return []


if __name__ == "__main__":
    filename = sys.argv[1]
    basename = os.path.splitext(os.path.basename(filename))[0]

    fnName = sys.argv[2]
    loopsFile = sys.argv[3]
    cvcPath = sys.argv[4]

    (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile)

    print("====== synthesis")
    invAndPs = [grammar(ci) for ci in loopAndPsInfo]

    lang = targetLang()

    candidates = synthesize(
        basename, lang, vars, invAndPs, preds, vc, loopAndPsInfo, cvcPath
    )
