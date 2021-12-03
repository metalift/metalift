import os
import sys

from analysis import CodeInfo
from ir import *
from actor_util import synthesize_actor
import actors.lattices as lat
from auto_grammar import auto_grammar

if True:
    from synthesize_rosette import synthesize
else:
    from synthesize_cvc5 import synthesize

synthStateStructure = [lat.MaxInt, lat.MaxInt]
synthStateType = Tuple(*[a[0] for a in synthStateStructure])


def grammarEquivalence(inputState, synthState):
    return auto_grammar(Bool(), 2, inputState, synthState)


def grammarStateInvariant(synthState):
    return auto_grammar(Bool(), 1, synthState)


def supportedCommand(inputState, synthState, args):
    return BoolLit(True)


def grammarQuery(ci: CodeInfo):
    name = ci.name

    inputState = ci.readVars[0]
    outputVar = ci.modifiedVars[0]

    summary = Eq(outputVar, auto_grammar(parseTypeRef(outputVar.type), 2, inputState))

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

        intLit = Choose(IntLit(0), IntLit(1))

        condition = Eq(inputAdd, intLit)

        intIn = Choose(stateVal1, stateVal2)

        intTransform = Choose(intIn, Add(intIn, intLit))

        intTransform = Choose(intTransform, Ite(condition, intTransform, intTransform))

        summary = Eq(
            outputState,
            MakeTuple(
                *[
                    synthStateStructure[i][1](TupleSel(inputState, i), intTransform)
                    for i in range(len(synthStateStructure))
                ]
            ),
        )

        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)


def initState():
    return MakeTuple(*[elem[2] for elem in synthStateStructure])


def targetLang():
    maxA = Var("a", Int())
    maxB = Var("b", Int())
    return [
        FnDeclNonRecursive("max", Int(), Ite(Ge(maxA, maxB), maxA, maxB), maxA, maxB),
    ]


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
