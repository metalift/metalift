from metalift.actors.search_structures import search_crdt_structures
from metalift.analysis import CodeInfo
from metalift.ir import *
from metalift.actors.synthesis import synthesize_actor
from metalift.actors.aci import check_aci
import metalift.actors.lattices as lat
from metalift.auto_grammar import auto_grammar, expand_lattice_logic
import sys
from metalift.maps_lang import mapsLang

from metalift.synthesize_auto import synthesize

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


def grammarStateInvariant(synthState, synthStateStructure):
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


def grammarSupportedCommand(synthState, args, synthStateStructure):
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


def inOrder(arg1, arg2):
    # adds win
    return Ite(
        Lt(arg1[1], arg2[1]),  # if clocks in order
        BoolLit(True),
        Ite(
            Eq(arg1[1], arg2[1]), # if clocks concurrent
            Ite(
                Eq(arg1[0], IntLit(1)), # if first is enable
                BoolLit(True), # second can be anything
                Not(Eq(arg2[0], IntLit(1))), # but if remove, must be remove next
            ),
            BoolLit(False), # clocks out of order
        )
    )

def opPrecondition(op):
    return Ge(op[1], IntLit(1))

def grammarQuery(ci: CodeInfo):
    name = ci.name

    summary = auto_grammar(ci.retT, base_depth + 1, *ci.readVars, enable_ite=True)

    return Synth(name, summary, *ci.readVars)


def grammar(ci: CodeInfo, synthStateStructure):
    name = ci.name

    if name.startswith("inv"):
        raise Exception("no invariant")
    else:  # ps
        inputState = ci.readVars[0]
        args = ci.readVars[1:]

        conditions = [Eq(args[0], BoolIntLit(1))]
        def fold_conditions(out):
            for c in conditions:
                out = Ite(c, out, out)
            return out

        out = MakeTuple(
            *[
                synthStateStructure[i].merge(
                    TupleGet(inputState, IntLit(i)),
                    fold_conditions(auto_grammar(TupleGet(inputState, IntLit(i)).type, base_depth, *args[1:]))
                )
                for i in range(len(synthStateStructure))
            ],
        )

        return Synth(name, out, *ci.modifiedVars, *ci.readVars)


def initState(synthStateStructure):
    return MakeTuple(
        *[auto_grammar(elem.ir_type(), 1, elem.bottom()) for elem in synthStateStructure]
    )

def targetLang():
    return mapsLang()


if __name__ == "__main__":
    mode = sys.argv[1]
    filename = "tests/actor_flag.ll"
    fnNameBase = "test"
    loopsFile = "tests/actor_flag.loops"
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

        search_crdt_structures(
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
            filename, fnNameBase, loopsFile, cvcPath, useOpList,
            lat.gen_structures(),
            stateTypeHint=BoolInt(),
            opArgTypeHint=[BoolInt(), ClockInt()],
            queryRetTypeHint=BoolInt(),
        )
