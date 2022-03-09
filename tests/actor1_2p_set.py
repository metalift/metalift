from analysis import CodeInfo
from ir import *
from actors.synthesis import synthesize_actor
from actors.aci import check_aci
import actors.lattices as lat
from auto_grammar import auto_grammar
import sys
import os

from synthesize_auto import synthesize

synthStateStructure = [lat.Set(Int()), lat.Set(Int())]
synthStateType = Tuple(*[a[0] for a in synthStateStructure])

fastDebug = False


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
    # removes win
    return Ite(
        Eq(arg1[0], IntLit(1)),  # if first command is insert
        BoolLit(True),  # second can be insert or remove
        Not(Eq(arg2[0], IntLit(1))),  # but if remove, must be remove next
    )


def grammarQuery(ci: CodeInfo):
    name = ci.name

    if not fastDebug:
        setContainTransformed = auto_grammar(Bool(), 3, *ci.readVars, enable_sets=True)
    else:  # hardcoded for quick debugging
        synthState = ci.readVars[0]

        setContainTransformed = Call(
            "set-member",
            Bool(),
            ci.readVars[1],
            Call(
                "set-minus",
                Set(Int()),
                Choose(
                    TupleGet(synthState, IntLit(0)), TupleGet(synthState, IntLit(1))
                ),
                TupleGet(synthState, IntLit(1)),
            ),
        )

    summary = Ite(setContainTransformed, IntLit(1), IntLit(0))

    return Synth(name, summary, *ci.readVars)


def grammar(ci: CodeInfo):
    name = ci.name

    if name.startswith("inv"):
        raise Exception("no invariant")
    else:  # ps
        inputState = ci.readVars[0]
        inputAdd = ci.readVars[1]
        inputValue = ci.readVars[2]

        condition = Eq(inputAdd, IntLit(1))
        setTransform = auto_grammar(Set(Int()), 1, inputValue, enable_sets=True)
        setTransform = Choose(setTransform, Ite(condition, setTransform, setTransform))

        summary = MakeTuple(
            *[
                synthStateStructure[i][1](
                    TupleGet(inputState, IntLit(i)), setTransform
                )
                for i in range(len(synthStateStructure))
            ],
        )

        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)


def initState():
    return MakeTuple(
        *[elem[2] for elem in synthStateStructure]
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
        useOpList = False
        if mode == "synth-debug":
            fastDebug = True
        elif mode == "synth-oplist":
            useOpList = True
        elif mode == "synth-debug-oplist":
            fastDebug = True
            useOpList = True

        out = synthesize_actor(
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
            useOpList = useOpList,
        )
