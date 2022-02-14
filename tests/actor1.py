from analysis import CodeInfo
from ir import *
from actor_util import synthesize_actor, check_aci
import actors.lattices as lat
from auto_grammar import auto_grammar
import sys

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


def supportedCommand(synthState, args):
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

    outputVar = ci.modifiedVars[0]

    setContainTransformed = auto_grammar(Bool(), 3, *ci.readVars, enable_sets=True)

    out = Ite(setContainTransformed, IntLit(1), IntLit(0))

    summary = Eq(outputVar, out)

    return Synth(name, summary, *ci.modifiedVars, *ci.readVars)


def grammar(ci: CodeInfo):
    name = ci.name

    if name.startswith("inv"):
        raise Exception("no invariant")
    else:  # ps
        inputState = ci.readVars[0]
        inputAdd = ci.readVars[1]
        inputValue = ci.readVars[2]

        outputState = ci.modifiedVars[0]

        condition = Eq(inputAdd, IntLit(1))
        setTransform = auto_grammar(Set(Int()), 1, inputValue, enable_sets=True)
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
    mode = sys.argv[1]
    filename = sys.argv[2]
    fnNameBase = sys.argv[3]
    loopsFile = sys.argv[4]
    cvcPath = sys.argv[5]

    if mode == "aci":
        check_aci(
            filename,
            fnNameBase,
            loopsFile,
            cvcPath,
        )
    else:
        synthesize_actor(
            filename,
            fnNameBase,
            loopsFile,
            cvcPath,
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
