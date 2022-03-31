from analysis import CodeInfo
from ir import *
from actors.synthesis import synthesize_actor
from actors.aci import check_aci
import actors.lattices as lat
from auto_grammar import auto_grammar
import rosette_translator
import sys
import os

from synthesize_auto import synthesize

synthStateStructure = [lat.MaxInt(), lat.MaxInt()]
synthStateType = Tuple(*[a.ir_type() for a in synthStateStructure])


def grammarEquivalence(inputState, synthState, queryParams):
    return auto_grammar(Bool(), 2, inputState, synthState, *queryParams)


def grammarStateInvariant(synthState):
    return auto_grammar(Bool(), 1, synthState)


def grammarSupportedCommand(synthState, args):
    return auto_grammar(Bool(), 1, synthState, *args)


def inOrder(cmd1, cmd2):
    return BoolLit(True)


def grammarQuery(ci: CodeInfo):
    name = ci.name

    inputState = ci.readVars[0]

    summary = auto_grammar(parseTypeRef(ci.retT), 2, inputState)

    return Synth(name, summary, *ci.modifiedVars, *ci.readVars)


def grammar(ci: CodeInfo):
    name = ci.name

    if name.startswith("inv"):
        raise Exception("no invariant")
    else:  # ps
        inputState = ci.readVars[0]
        stateVal1 = TupleGet(inputState, IntLit(0))
        stateVal2 = TupleGet(inputState, IntLit(1))

        inputAdd = ci.readVars[1]

        intLit = Choose(IntLit(0), IntLit(1))

        condition = Eq(inputAdd, intLit)

        intIn = Choose(stateVal1, stateVal2)

        intTransform = Choose(intIn, Add(intIn, intLit))

        intTransform = Choose(intTransform, Ite(condition, intTransform, intTransform))

        summary = MakeTuple(
            *[
                synthStateStructure[i].merge(
                    TupleGet(inputState, IntLit(i)), intTransform
                )
                for i in range(len(synthStateStructure))
            ]
        )

        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)


def initState():
    return MakeTuple(*[elem.bottom() for elem in synthStateStructure])


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
            lambda _: BoolLit(True),
            grammar,
            grammarQuery,
            grammarEquivalence,
            targetLang,
            synthesize,
            unboundedInts=True,
            useOpList=useOpList,
            listBound=2,
        )
