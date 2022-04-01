from analysis import CodeInfo
from ir import *
from actors.synthesis import synthesize_actor
from actors.aci import check_aci
import actors.lattices as lat
from auto_grammar import auto_grammar
import sys
import os

from synthesize_auto import synthesize

synthStateStructure = [lat.Map(OpaqueInt(), lat.PosBool()), lat.Map(OpaqueInt(), lat.PosBool())]
synthStateType = Tuple(*[a.ir_type() for a in synthStateStructure])

fastDebug = False
base_depth = 1


def grammarEquivalence(inputState, synthState, queryParams):
    core = auto_grammar(
        Bool(), # query return type?
        base_depth + 1,
        inputState, synthState, *queryParams,
        Call(
            "map-get",
            Bool(),
            Choose(
                TupleGet(synthState, IntLit(0)),
                TupleGet(synthState, IntLit(1))
            ),
            queryParams[0],
            BoolLit(False)
        )
    )
    return Choose(
        core,
        Eq(core, core)
    )


def grammarStateInvariant(synthState):
    return auto_grammar(Bool(), base_depth, synthState)


def grammarSupportedCommand(synthState, args):
    conditions = [Eq(args[0], IntLit(1))]

    merge_a = Var("merge_a", Bool())
    merge_b = Var("merge_b", Bool())

    out = auto_grammar(
        Bool(), base_depth,
        synthState, *args[1:],
        Call( # does the remove set have any true values?
            "map-fold-values",
            Bool(),
            Choose(
                TupleGet(synthState, IntLit(0)),
                TupleGet(synthState, IntLit(1))
            ),
            Lambda(
                Bool(),
                Or(merge_a, merge_b),
                merge_a, merge_b
            ),
            BoolLit(False)
        )
    )

    for c in conditions:
        out = Ite(c, out, out)

    return out


def inOrder(arg1, arg2):
    # removes win
    return Ite(
        Eq(arg1[0], IntLit(1)),  # if first command is insert
        BoolLit(True),  # second can be insert or remove
        Not(Eq(arg2[0], IntLit(1))),  # but if remove, must be remove next
    )


def grammarQuery(ci: CodeInfo):
    name = ci.name

    setContainTransformed = auto_grammar(
        Bool(), base_depth + 1,
        *ci.readVars,
        Call(
            "map-get",
            Bool(),
            Choose(
                TupleGet(ci.readVars[0], IntLit(0)),
                TupleGet(ci.readVars[0], IntLit(1))
            ),
            ci.readVars[1],
            BoolLit(False)
        )
    )

    summary = Ite(setContainTransformed, IntLit(1), IntLit(0))

    return Synth(name, summary, *ci.readVars)


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

        out = MakeTuple(
            *[
                synthStateStructure[i].merge(
                    TupleGet(inputState, IntLit(i)),
                    fold_conditions(auto_grammar(
                        TupleGet(inputState, IntLit(i)).type, base_depth,
                        *args[1:],
                        Call("map-create", Map(OpaqueInt(), Bool())),
                        Call(
                            "map-singleton",
                            Map(OpaqueInt(), Bool()),
                            args[1],
                            BoolLit(True)
                        )
                    ))
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

def opPrecondition(op):
    return Ge(op[2], IntLit(1))

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
            opArgTypeHint=[EnumInt(), OpaqueInt(), ClockInt()],
            queryArgTypeHint=[OpaqueInt()],
            useOpList = useOpList,
            listBound=2,
        )
