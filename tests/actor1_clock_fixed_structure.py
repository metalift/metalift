from metalift.analysis import CodeInfo
from metalift.ir import *
from metalift.actors.synthesis import synthesize_actor
from metalift.actors.aci import check_aci
import metalift.actors.lattices as lat
from metalift.actors.auto_grammar import auto_grammar, expand_lattice_logic
import sys
import os
from metalift.maps_lang import mapsLang

from metalift.synthesize_auto import synthesize

synthStateStructure = [lat.Map(OpaqueInt(), lat.MaxInt(ClockInt())), lat.Map(OpaqueInt(), lat.MaxInt(ClockInt()))]
synthStateType = TupleT(*[a.ir_type() for a in synthStateStructure])

base_depth = 1

def fold_conditions(out, conditions):
    for c in conditions:
        out = Ite(c, out, out)
    return out

def grammarEquivalence(inputState, synthState, queryParams):
    return auto_grammar(
        Bool(),
        base_depth,
        inputState, synthState, *queryParams
    )


def grammarStateInvariant(synthState):
    state_valid = And(*[
        synthStateStructure[i].check_is_valid(
            TupleGet(synthState, IntLit(i))
        )
        for i in range(len(synthStateStructure))
    ])

    return And(
        state_valid,
        auto_grammar(Bool(), base_depth, synthState)
    )


def grammarSupportedCommand(synthState, args):
    conditions = [Eq(a, IntLit(1)) for a in args if a.type == BoolInt()]

    out = auto_grammar(
        Bool(), base_depth + 1,
        synthState, *args,
        *expand_lattice_logic(*[
            (TupleGet(synthState, IntLit(i)), synthStateStructure[i])
            for i in range(len(synthStateStructure))
        ]),
        enable_ite=True
    )

    return fold_conditions(out, conditions)

def grammarQuery(ci: CodeInfo):
    name = ci.name

    if ci.retT == BoolInt():
        condition = auto_grammar(
            Bool(),
            base_depth + 2,
            *ci.readVars
        )

        summary = Ite(condition, IntLit(1), IntLit(0))
    else:
        summary = auto_grammar(
            parseTypeRef(ci.retT), base_depth + 2,
            *ci.readVars,
            enable_ite=True
        )

    return Synth(name, summary, *ci.readVars)


def grammar(ci: CodeInfo):
    name = ci.name

    if name.startswith("inv"):
        raise Exception("no invariant")
    else:  # ps
        inputState = ci.readVars[0]
        args = ci.readVars[1:]

        conditions = [Eq(a, IntLit(1)) for a in args if a.type == BoolInt()]
        
        out = Tuple(
            *[
                synthStateStructure[i].merge(
                    TupleGet(inputState, IntLit(i)),
                    fold_conditions(auto_grammar(
                        TupleGet(inputState, IntLit(i)).type,
                        base_depth,
                        *args[1:]
                    ), conditions)
                )
                for i in range(len(synthStateStructure))
            ],
        )

        return Synth(name, out, *ci.modifiedVars, *ci.readVars)


def initState():
    return Tuple(
        *[elem.bottom() for elem in synthStateStructure]
    )

def targetLang():
    return mapsLang()

benchmarks = {
    "add_wins": {
        "inOrder": lambda arg1, arg2: Ite(
            Lt(arg1[-1], arg2[-1]),  # if clocks in order
            BoolLit(True),
            Ite(
                Eq(arg1[-1], arg2[-1]), # if clocks concurrent
                Ite(
                    Eq(arg1[0], IntLit(1)),  # if first command is insert
                    Eq(arg2[0], IntLit(1)), # second command must be insert
                    BoolLit(True),  # second can be insert or remove
                ),
                BoolLit(False), # clocks out of order
            )
        ),
        "opPrecondition": lambda op: Ge(op[-1], IntLit(1))
    },
    "remove_wins": {
        "inOrder": lambda arg1, arg2: Ite(
            Lt(arg1[-1], arg2[-1]),  # if clocks in order
            BoolLit(True),
            Ite(
                Eq(arg1[-1], arg2[-1]), # if clocks concurrent
                Ite(
                    Eq(arg1[0], IntLit(1)),  # if first command is insert
                    BoolLit(True),  # second can be insert or remove
                    Not(Eq(arg2[0], IntLit(1))),  # but if remove, must be remove next
                ),
                BoolLit(False), # clocks out of order
            )
        ),
        "opPrecondition": lambda op: Ge(op[-1], IntLit(1))
    }
}

if __name__ == "__main__":
    mode = sys.argv[1]
    bench = sys.argv[2]
    filename = "tests/actor1_clock.ll"
    fnNameBase = "test"
    loopsFile = "tests/actor1_clock.loops"
    cvcPath = "cvc5"

    useOpList = False
    if mode == "synth-oplist":
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
        benchmarks[bench]["inOrder"],
        benchmarks[bench]["opPrecondition"],
        grammar,
        grammarQuery,
        grammarEquivalence,
        targetLang,
        synthesize,
        stateTypeHint=Set(OpaqueInt()),
        opArgTypeHint=[BoolInt(), OpaqueInt(), ClockInt()],
        queryArgTypeHint=[OpaqueInt()],
        queryRetTypeHint=BoolInt(),
        useOpList = useOpList,
        listBound=2,
    )
