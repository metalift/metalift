from actors.search_structures import search_crdt_structures
from analysis import CodeInfo
from ir import *
from actors.synthesis import synthesize_actor
from actors.aci import check_aci
import actors.lattices as lat
from auto_grammar import auto_grammar
import sys

from synthesize_auto import synthesize

synthStateStructure = [lat.CascadingTuple(lat.VectorClockLattice(), lat.PosBool()), lat.PosBool()]
synthStateType = Tuple(*[a.ir_type() for a in synthStateStructure])

base_depth = 1

def grammarEquivalence(inputState, synthState):
    return auto_grammar(
        Bool(), base_depth + 1, inputState, synthState,
        enable_ite=True
    )


def grammarStateInvariant(synthState):
    return auto_grammar(Bool(), base_depth, synthState)


def grammarSupportedCommand(synthState, args):
    conditions = [Eq(args[0], EnumIntLit(1))]

    out = auto_grammar(Bool(), base_depth + 1, synthState, *args, enable_ite=True)
    for c in conditions:
        out = Ite(c, out, out)

    return out


def inOrder(arg1, arg2):
    current_vector_clock = TupleGet(TupleGet(
        Var("i11_for_state_transition", Tuple(Tuple(VectorClock(), Bool()), Bool())),
        IntLit(0)
    ), IntLit(0))
    # adds win
    return And(
        Ge(arg2[1], current_vector_clock), # we cannot have an operation strictly from the past
        Le(arg1[1], arg2[1]), # clocks must not be out of order
        Ite(
            Lt(current_vector_clock, arg2[1]),  # if clocks in order    
            BoolLit(True),
            Ite( # if clocks concurrent
                Eq(arg1[0], IntLit(1)), # if first is enable
                Eq(arg2[0], IntLit(1)), # second must be enable
                BoolLit(True), # but if remove, can be anything next
            ),
        )
    )

def opPrecondition(op):
    return Gt(op[1], Lit(0, VectorClock()))

def grammarQuery(ci: CodeInfo):
    name = ci.name

    summary = auto_grammar(ci.retT, base_depth + 1, *ci.readVars, enable_ite=True)

    return Synth(name, summary, *ci.readVars)


def grammar(ci: CodeInfo):
    name = ci.name

    if name.startswith("inv"):
        raise Exception("no invariant")
    else:  # ps
        inputState = ci.readVars[0]
        args = ci.readVars[1:]

        conditions = [Eq(args[0], EnumIntLit(1))]
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


def initState():
    return MakeTuple(
        *[auto_grammar(elem.ir_type(), 1, elem.bottom()) for elem in synthStateStructure]
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
            stateTypeHint=EnumInt(),
            opArgTypeHint=[EnumInt(), VectorClock()],
            queryRetTypeHint=EnumInt(),
            useOpList = useOpList,
            listBound=2,
        )
