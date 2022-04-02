from analysis import CodeInfo
from ir import *
from actors.synthesis import synthesize_actor
from actors.aci import check_aci
import actors.lattices as lat
from auto_grammar import auto_grammar
import sys
import os

from synthesize_auto import synthesize

base_depth = 1

synthStateStructure = [lat.Set(Int())]
synthStateType = Tuple(
    *[a.ir_type() for a in synthStateStructure], Int()
)  # TODO(shadaj): automate insertion of dummy


def grammarEquivalence(inputState, synthState, queryParams):
    inputCalc = auto_grammar(
        Bool(), # query return type?
        base_depth,
        inputState, *queryParams,
    )

    synthCalc = Eq(Call(
        "test_response",
        Int(), # query return type?
        synthState, *queryParams,
    ), IntLit(1))

    random = auto_grammar(
        Bool(),
        base_depth,
        inputState, synthState, *queryParams
    )

    return Choose(
        random,
        And(
            Eq(inputCalc, synthCalc),
            random
        )
    )


def grammarStateInvariant(synthState):
    return auto_grammar(Bool(), base_depth, synthState)


def grammarSupportedCommand(synthState, args):
    conditions = [Eq(args[0], IntLit(1))]

    out = auto_grammar(Bool(), base_depth, synthState, *args[1:])
    for c in conditions:
        out = Ite(c, out, out)

    return out


def inOrder(arg1, arg2):
    # adds win
    return Ite(
        Eq(arg1[0], IntLit(1)),  # if first command is insert
        Eq(arg2[0], IntLit(1)),  # second must be insert
        BoolLit(True),  # but if remove, can be anything next
    )


def grammarQuery(ci: CodeInfo):
    name = ci.name

    setContainTransformed = auto_grammar(Bool(), base_depth + 1, *ci.readVars)

    summary = Ite(setContainTransformed, IntLit(1), IntLit(0))

    return Synth(name, summary, *ci.modifiedVars, *ci.readVars)


def grammar(ci: CodeInfo):
    name = ci.name

    if name.startswith("inv"):
        raise Exception("no invariant")
    else:  # ps
        inputState = ci.readVars[0]
        args = ci.readVars[1:]

        conditions = [Eq(args[0], IntLit(1))]
        def fold_conditions(out):
            for c in conditions:
                out = Ite(c, out, out)
            return out

        summary = MakeTuple(
            *[
                synthStateStructure[i].merge(
                    TupleGet(inputState, IntLit(i)),
                    fold_conditions(auto_grammar(TupleGet(inputState, IntLit(i)).type, base_depth, *args[1:]))
                )
                for i in range(len(synthStateStructure))
            ],
            IntLit(0),  # TODO(shadaj): automate insertion of dummy
        )

        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)


def initState():
    return MakeTuple(
        *[elem.bottom() for elem in synthStateStructure],
        IntLit(0),  # TODO(shadaj): automate insertion of dummy
    )


def targetLang():
    return []


if __name__ == "__main__":
    mode = sys.argv[1]
    filename = "tests/actor1.ll"
    fnNameBase = "test"
    loopsFile = "tests/actor1.loops"
    cvcPath = "cvc5"

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
            useOpList=useOpList,
            listBound=2,
        )
