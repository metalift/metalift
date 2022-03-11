from actors.search_structures import search_crdt_structures
from analysis import CodeInfo
from ir import *
from actors.synthesis import synthesize_actor
from actors.aci import check_aci
import actors.lattices as lat
from auto_grammar import auto_grammar
import sys

from synthesize_auto import synthesize


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

    setContainTransformed = auto_grammar(Bool(), 3, *ci.readVars, enable_sets=True)

    summary = Ite(setContainTransformed, IntLit(1), IntLit(0))

    return Synth(name, summary, *ci.readVars)


def grammar(ci: CodeInfo, synthStateStructure):
    name = ci.name

    if name.startswith("inv"):
        raise Exception("no invariant")
    else:  # ps
        inputState = ci.readVars[0]
        inputAdd = ci.readVars[1]
        inputValue = ci.readVars[2]

        condition = Eq(inputAdd, IntLit(1))

        summary = MakeTuple(
            *[
                synthStateStructure[i][1](
                    TupleGet(inputState, IntLit(i)),
                    Ite(
                        condition,
                        auto_grammar(TupleGet(inputState, IntLit(i)).type, 1, inputValue, enable_sets=True),
                        auto_grammar(TupleGet(inputState, IntLit(i)).type, 1, inputValue, enable_sets=True),
                    )
                )
                for i in range(len(synthStateStructure))
            ],
        )

        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)


def initState(synthStateStructure):
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
        if mode == "synth-oplist":
            useOpList = True

        structureCandidates = iter([
            [lat.MaxInt, lat.MaxInt],
            [lat.Set(Int()), lat.Set(Int())],
            [lat.Set(Int()), lat.Set(Int()), lat.Set(Int())],
        ])

        search_crdt_structures(
            initState,
            grammarStateInvariant,
            grammarSupportedCommand,
            inOrder,
            grammar,
            grammarQuery,
            grammarEquivalence,
            targetLang,
            synthesize,
            filename, fnNameBase, loopsFile, cvcPath, useOpList,
            structureCandidates
        )
