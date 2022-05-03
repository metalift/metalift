from metalift.analysis import CodeInfo
from ir import *
from actors.synthesis import synthesize_actor
from actors.aci import check_aci
import actors.lattices as lat
from metalift.auto_grammar import auto_grammar, expand_lattice_logic
import sys
import os
from maps_lang import mapsLang

from synthesize_auto import synthesize

synthStateStructure = [lat.CascadingTuple(lat.MaxInt(ClockInt()), lat.MaxInt(Int())), lat.MaxInt(BoolInt())]
synthStateType = Tuple(*[a.ir_type() for a in synthStateStructure])

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
        
        out = MakeTuple(
            *[
                synthStateStructure[i].merge(
                    TupleGet(inputState, IntLit(i)),
                    fold_conditions(auto_grammar(
                        TupleGet(inputState, IntLit(i)).type,
                        base_depth,
                        *args
                    ), conditions)
                )
                for i in range(len(synthStateStructure))
            ],
        )

        return Synth(name, out, *ci.modifiedVars, *ci.readVars)


def initState():
    return MakeTuple(
        *[elem.bottom() for elem in synthStateStructure]
    )

def targetLang():
    return mapsLang()

benchmarks = {
    "lww_max": {
        "inOrder": lambda arg1, arg2: Ite(
            Lt(arg1[-1], arg2[-1]),  # if clocks in order
            BoolLit(True),
            Ite(
                Eq(arg1[-1], arg2[-1]), # if clocks concurrent
                Ge(arg2[0], arg1[0]),  # second command must have a higher value
                BoolLit(False), # clocks out of order
            )
        ),
        "opPrecondition": lambda op: Ge(op[-1], IntLit(1))
    }
}

if __name__ == "__main__":
    mode = sys.argv[1]
    bench = sys.argv[2]
    filename = "tests/actor_register.ll"
    fnNameBase = "test"
    loopsFile = "tests/actor_register.loops"
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
        stateTypeHint=Int(),
        opArgTypeHint=[Int(), ClockInt()],
        queryArgTypeHint=[],
        queryRetTypeHint=Int(),
        useOpList = useOpList,
        listBound=2,
    )
