from analysis import CodeInfo
from ir import *
from actors.synthesis import synthesize_actor
from actors.aci import check_aci
import actors.lattices as lat
from auto_grammar import auto_grammar
import sys
import os
from maps_lang import mapsLang

from synthesize_auto import synthesize

synthStateStructure = [lat.Set(OpaqueInt()), lat.Set(OpaqueInt())]
synthStateType = Tuple(*[a.ir_type() for a in synthStateStructure])

fastDebug = False
base_depth = 1


def grammarEquivalence(inputState, synthState, queryParams):
    return auto_grammar(
        Bool(),
        base_depth,
        inputState, synthState, *queryParams
    )


def grammarStateInvariant(synthState, boost):
    return auto_grammar(Bool(), base_depth, synthState)


def grammarSupportedCommand(synthState, args, boost):
    conditions = [Eq(args[0], IntLit(1))]

    out = auto_grammar(Bool(), base_depth, synthState, *args[1:])
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

    if not fastDebug:
        setContainTransformed = auto_grammar(Bool(), base_depth + 1, *ci.readVars)
    else:  # hardcoded for quick debugging
        synthState = ci.readVars[0]

        setContainTransformed = Call(
            "set-member",
            Bool(),
            ci.readVars[1],
            Call(
                "set-minus",
                Set(Int()),
                Choose(
                    TupleGet(synthState, IntLit(0)), TupleGet(synthState, IntLit(1))
                ),
                TupleGet(synthState, IntLit(1)),
            ),
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
                    fold_conditions(auto_grammar(TupleGet(inputState, IntLit(i)).type, base_depth, *args[1:]))
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
            lambda _: BoolLit(True),
            grammar,
            grammarQuery,
            grammarEquivalence,
            targetLang,
            synthesize,
            stateTypeHint=Set(OpaqueInt()),
            opArgTypeHint=[BoolInt(), OpaqueInt()],
            queryArgTypeHint=[OpaqueInt()],
            useOpList = useOpList,
            listBound=2,
        )
