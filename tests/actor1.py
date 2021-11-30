import os
import sys

from analysis import CodeInfo
from ir import *
from actor_util import synthesize_actor
import actors.lattices as lat

if False:
    from synthesize_rosette import synthesize
else:
    from synthesize_cvc5 import synthesize

synthStateStructure = [lat.Set(Int()), lat.Set(Int())]
synthStateType = Tuple(*[a[0] for a in synthStateStructure])


def grammarEquivalence(inputState, synthState):
    setIn = Choose(inputState, TupleSel(synthState, 0), TupleSel(synthState, 1))

    setIn = Choose(setIn, Call("setminus", Set(Int()), setIn, setIn))

    equivalent = Eq(setIn, setIn)

    return equivalent


def grammarStateInvariant(synthState):
    setIn = Choose(TupleSel(synthState, 0), TupleSel(synthState, 1))

    valid = Choose(BoolLit(True), Call("subset", Bool(), setIn, setIn))

    return valid


def supportedCommand(inputState, synthState, args):
    add = args[0]
    value = args[1]

    return Ite(
        Eq(add, IntLit(1)),
        # insertion works if the elem is not in both sets
        # so the sets are saturated
        Not(
            And(
                Call("member", Bool(), value, TupleSel(synthState, 0)),
                Call("member", Bool(), value, TupleSel(synthState, 1)),
            )
        ),
        # deletion can work even if not in the insertion set
        # because we can just add the element to both sets
        # which results in an observed-equivalent final state
        BoolLit(True),
    )


def grammarQuery(ci: CodeInfo):
    name = ci.name

    inputState = ci.readVars[0]
    outputVar = ci.modifiedVars[0]

    stateSet1 = TupleSel(inputState, 0)
    stateSet2 = TupleSel(inputState, 1)

    inputValue = ci.readVars[1]

    setIn = Choose(stateSet1, stateSet2)
    setContains = Call("member", Bool(), inputValue, setIn)

    setContainTransformed = Choose(setContains, Not(setContains))

    setContainTransformed = Choose(
        setContainTransformed, And(setContainTransformed, setContainTransformed)
    )

    intLit = Choose(IntLit(0), IntLit(1))

    out = Ite(setContainTransformed, intLit, intLit)

    summary = Eq(outputVar, out)

    return Synth(name, summary, *ci.modifiedVars, *ci.readVars)


def grammar(ci: CodeInfo):
    name = ci.name

    if name.startswith("inv"):
        raise Exception("no invariant")
    else:  # ps
        inputState = ci.readVars[0]
        stateSet1 = TupleSel(inputState, 0)
        stateSet2 = TupleSel(inputState, 1)

        inputAdd = ci.readVars[1]
        inputValue = ci.readVars[2]

        outputState = ci.modifiedVars[0]

        intLit = Choose(IntLit(0), IntLit(1))

        condition = Eq(inputAdd, intLit)

        setIn = Choose(
            stateSet1,
            stateSet2,
            Call("singleton", Set(Int()), inputValue),
        )

        setTransform = setIn

        setTransform = Choose(setTransform, Ite(condition, setTransform, setTransform))

        summary = Eq(
            outputState,
            MakeTuple(
                *[
                    synthStateStructure[i][1](TupleSel(inputState, i), setTransform)
                    for i in range(len(synthStateStructure))
                ]
            ),
        )

        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)


def initState():
    return MakeTuple(*[elem[2] for elem in synthStateStructure])


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
