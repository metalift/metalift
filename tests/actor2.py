import os
import sys

from analysis import CodeInfo
from ir import *
from actor_util import synthesize_actor

if True:
    from synthesize_rosette import synthesize
else:
    from synthesize_cvc5 import synthesize

synthStateType = Tuple(Int(), Int())


def grammarEquivalence():
    inputState = Var("inputState", Int())
    synthState = Var("synthState", synthStateType)

    synthElem = Choose(TupleSel(synthState, 0), TupleSel(synthState, 1))
    equivalent = Eq(inputState, Sub(synthElem, synthElem))

    return Synth("equivalence", equivalent, inputState, synthState)


def grammarStateInvariant():
    synthState = Var("synthState", synthStateType)

    valid = Choose(BoolLit(True), BoolLit(False))

    return Synth("stateInvariant", valid, synthState)


def supportedCommand(synthState, args):
    add = args[0]

    return Ite(
        Eq(add, IntLit(1)),
        BoolLit(True),
        Gt(TupleSel(synthState, 0), TupleSel(synthState, 1)),
    )


def grammarQuery(ci: CodeInfo):
    name = ci.name

    inputState = ci.readVars[0]
    outputVar = ci.modifiedVars[0]

    inputInt = Choose(TupleSel(inputState, 0), TupleSel(inputState, 1))

    summary = Eq(outputVar, Sub(inputInt, inputInt))

    return Synth(name, summary, *ci.modifiedVars, *ci.readVars)


def grammar(ci: CodeInfo):
    name = ci.name

    if name.startswith("inv"):
        raise Exception("no invariant")
    else:  # ps
        inputState = ci.readVars[0]
        stateVal1 = TupleSel(inputState, 0)
        stateVal2 = TupleSel(inputState, 1)

        inputAdd = ci.readVars[1]

        outputState = ci.modifiedVars[0]

        condition = Eq(inputAdd, Choose(IntLit(0), IntLit(1)))

        intLit = Choose(IntLit(0), IntLit(1))

        intIn = Choose(stateVal1, stateVal2)

        intTransform = Choose(intIn, Add(intIn, intLit))

        chosenTransform = Choose(
            intTransform, Ite(condition, intTransform, intTransform)
        )

        summary = Eq(outputState, MakeTuple(chosenTransform, chosenTransform))

        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)


def initState():
    return MakeTuple(IntLit(0), IntLit(0))


def targetLang():
    return []


if __name__ == "__main__":
    synthesize_actor(
        synthStateType,
        initState,
        grammarStateInvariant,
        supportedCommand,
        grammar,
        grammarQuery,
        grammarEquivalence,
        targetLang,
        synthesize,
    )
