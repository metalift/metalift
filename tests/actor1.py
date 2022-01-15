from analysis import CodeInfo
from ir import *
from actor_util import synthesize_actor, check_aci
import actors.lattices as lat
from auto_grammar import auto_grammar

if True:
    from synthesize_rosette import synthesize
else:
    from synthesize_cvc5 import synthesize

synthStateStructure = [lat.Set(Int()), lat.Set(Int())]
synthStateType = Tuple(*[a[0] for a in synthStateStructure])


def grammarEquivalence(inputState, synthState):
    return auto_grammar(Bool(), 2, inputState, synthState, enable_sets=True)


def grammarStateInvariant(synthState):
    return auto_grammar(Bool(), 1, synthState, enable_sets=True)


def supportedCommand(inputState, synthState, args):
    add = args[0]
    value = args[1]

    return Ite(
        Eq(add, IntLit(1)),
        # insertion works if the elem is not in both sets
        # so the sets are saturated
        Not(
            And(
                Call("set-member", Bool(), value, TupleGet(synthState, IntLit(0))),
                Call("set-member", Bool(), value, TupleGet(synthState, IntLit(1))),
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

    stateSet1 = TupleGet(inputState, IntLit(0))
    stateSet2 = TupleGet(inputState, IntLit(1))

    inputValue = ci.readVars[1]

    setIn = Choose(stateSet1, stateSet2)
    setContains = Call("set-member", Bool(), inputValue, setIn)

    setContainTransformed = Choose(setContains, Not(setContains))

    setContainTransformed = Choose(
        setContainTransformed, And(setContainTransformed, setContainTransformed)
    )

    out = Ite(setContainTransformed, IntLit(1), IntLit(0))

    summary = Eq(outputVar, out)

    return Synth(name, summary, *ci.modifiedVars, *ci.readVars)


def grammar(ci: CodeInfo):
    name = ci.name

    if name.startswith("inv"):
        raise Exception("no invariant")
    else:  # ps
        inputState = ci.readVars[0]
        stateSet1 = TupleGet(inputState, IntLit(0))
        stateSet2 = TupleGet(inputState, IntLit(1))

        inputAdd = ci.readVars[1]
        inputValue = ci.readVars[2]

        outputState = ci.modifiedVars[0]

        condition = Eq(inputAdd, IntLit(1))

        setIn = Choose(
            stateSet1,
            stateSet2,
            Call("set-singleton", Set(Int()), inputValue),
        )

        setTransform = setIn

        setTransform = Choose(setTransform, Ite(condition, setTransform, setTransform))

        summary = Eq(
            outputState,
            MakeTuple(
                *[
                    synthStateStructure[i][1](
                        TupleGet(inputState, IntLit(i)), setTransform
                    )
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
    check_aci()
    # synthesize_actor(
    #     synthStateType,
    #     initState,
    #     grammarStateInvariant,
    #     supportedCommand,
    #     grammar,
    #     grammarQuery,
    #     grammarEquivalence,
    #     targetLang,
    #     synthesize,
    # )
