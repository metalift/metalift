from actors.search_structures import search_crdt_structures
from analysis import CodeInfo
from ir import *
from actors.synthesis import synthesize_actor
from actors.aci import check_aci
import actors.lattices as lat
from auto_grammar import auto_grammar
import sys

from synthesize_auto import synthesize

base_depth = 1

def grammarEquivalence(inputState, synthState, queryParams):
    return auto_grammar(
        Bool(), base_depth + 1, inputState, synthState, *queryParams,
        enable_ite=True
    )


def grammarStateInvariant(synthState):
    return auto_grammar(Bool(), base_depth, synthState)


def grammarSupportedCommand(synthState, args):
    conditions = [Eq(args[0], BoolIntLit(1))]

    out = auto_grammar(Bool(), base_depth + 1, synthState, *args, enable_ite=True)
    for c in conditions:
        out = Ite(c, out, out)

    return out


def inOrder(arg1, arg2):
    # adds win
    return Ite(
        Lt(arg1[1], arg2[1]),  # if clocks in order
        BoolLit(True),
        Ite(
            Eq(arg1[1], arg2[1]), # if clocks concurrent
            Ite(
                Eq(arg1[0], IntLit(1)), # if first is enable
                Eq(arg2[0], IntLit(1)), # second must be enable
                BoolLit(True), # but if remove, can be anything next
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
        *[elem.bottom() for elem in synthStateStructure]
    )

def targetLang():
    return []


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
            filename, fnNameBase, loopsFile, cvcPath,
            useOpList,
            lat.gen_structures(),
            stateTypeHint=BoolInt(),
            opArgTypeHint=[BoolInt(), ClockInt()],
            queryRetTypeHint=BoolInt(),
        )
