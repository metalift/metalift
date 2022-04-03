from analysis import CodeInfo
from ir import *
from actors.synthesis import synthesize_actor
from actors.aci import check_aci
import actors.lattices as lat
from auto_grammar import auto_grammar, expand_lattice_logic
import sys
import os

from synthesize_auto import synthesize

synthStateStructure = [lat.Map(OpaqueInt(), lat.MaxInt(ClockInt())), lat.Map(OpaqueInt(), lat.MaxInt(ClockInt()))]
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
    conditions = [Eq(a, auto_grammar(BoolInt(), 0)) for a in args if a.type == BoolInt()]

    out = auto_grammar(
        Bool(), base_depth + 1,
        synthState, *args[1:],
        *expand_lattice_logic(*[
            (TupleGet(synthState, IntLit(i)), synthStateStructure[i])
            for i in range(len(synthStateStructure))
        ])
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

        summary = auto_grammar(BoolInt(), 0)
        for _ in range(base_depth):
            summary = Choose(summary, Ite(
                condition,
                auto_grammar(BoolInt(), 0),
                summary
            ))
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

        conditions = [Eq(a, auto_grammar(a.type, 0)) for a in args if a.type == BoolInt()]
        
        out = MakeTuple(
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
    return MakeTuple(
        *[elem.bottom() for elem in synthStateStructure]
    )

def targetLang():
    return []

def inOrder(arg1, arg2):
    # removes win
    return Ite(
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
    )

def opPrecondition(op):
    return Ge(op[-1], IntLit(1))

if __name__ == "__main__":
    mode = sys.argv[1]
    filename = "tests/actor1_clock.ll"
    fnNameBase = "test"
    loopsFile = "tests/actor1_clock.loops"
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
            opPrecondition,
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
