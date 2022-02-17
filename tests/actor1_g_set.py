from analysis import CodeInfo
from ir import *
from actors.synthesis import synthesize_actor, check_aci
import actors.lattices as lat
from auto_grammar import auto_grammar
import sys
import os

if os.environ.get("SYNTH_CVC5") == "1":
    from synthesize_cvc5 import synthesize
else:
    from synthesize_rosette import synthesize

synthStateStructure = [lat.Set(Int())]
synthStateType = Tuple(
    *[a[0] for a in synthStateStructure], Int()
)  # TODO(shadaj): automate insertion of dummy


def grammarEquivalence(inputState, synthState):
    return auto_grammar(Bool(), 2, inputState, synthState, enable_sets=True)


def grammarStateInvariant(synthState):
    return auto_grammar(Bool(), 1, synthState, enable_sets=True)


def grammarSupportedCommand(synthState, args):
    add = args[0]

    return Ite(
        Eq(add, IntLit(1)),
        auto_grammar(Bool(), 1, synthState, enable_sets=True),
        auto_grammar(Bool(), 1, synthState, enable_sets=True),
    )


def inOrder(arg1, arg2):
    # adds win
    return Ite(
        Eq(arg1[0], IntLit(1)),  # if first command is insert
        Eq(arg2[0], IntLit(1)),  # second must be insert
        BoolLit(True),  # but if remove, can be anything next
    )


def grammarQuery(ci: CodeInfo):
    name = ci.name

    outputVar = ci.modifiedVars[0]

    synthState = ci.readVars[0]

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
                ],
                IntLit(0),  # TODO(shadaj): automate insertion of dummy
            ),
        )

        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)


def initState():
    return MakeTuple(
        *[elem[2] for elem in synthStateStructure],
        IntLit(0),  # TODO(shadaj): automate insertion of dummy
    )


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
            grammarSupportedCommand,
            inOrder,
            grammar,
            grammarQuery,
            grammarEquivalence,
            targetLang,
            synthesize,
        )
