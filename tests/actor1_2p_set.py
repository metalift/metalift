from analysis import CodeInfo
from ir import *
from actors.synthesis import synthesize_actor
from actors.aci import check_aci
import actors.lattices as lat
from auto_grammar import auto_grammar
import sys
import os

from synthesize_auto import synthesize

synthStateStructure = [lat.Set(Int()), lat.Set(Int())]
opType = Tuple(Int(), Int())
synthStateType = Tuple(*[a[0] for a in synthStateStructure], List(opType))

def unpackOp(op):
    return [
        TupleGet(op, IntLit(i))
        for i in range(len(opType.args))
    ]

fastDebug = False


def grammarEquivalence(inputState, synthState):
    return auto_grammar(Bool(), 2, inputState, synthState, enable_sets=True)


def grammarStateInvariant(synthState):
    return auto_grammar(Bool(), 1, synthState, enable_sets=True)


def grammarSupportedCommand(synthState, args):
    add = args[0]

    return Ite(
        Eq(add, IntLit(1)),
        auto_grammar(Bool(), 1, synthState, enable_sets=True),
        auto_grammar(Bool(), 1, synthState, enable_sets=True),
    )


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
        setContainTransformed = auto_grammar(Bool(), 3, *ci.readVars, enable_sets=True)
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
        inputAdd = ci.readVars[1]
        inputValue = ci.readVars[2]

        condition = Eq(inputAdd, IntLit(1))
        setTransform = auto_grammar(Set(Int()), 1, inputValue, enable_sets=True)
        setTransform = Choose(setTransform, Ite(condition, setTransform, setTransform))

        summary = MakeTuple(
            *[
                synthStateStructure[i][1](
                    TupleGet(inputState, IntLit(i)), setTransform
                )
                for i in range(len(synthStateStructure))
            ],
            Call(
                "list_prepend",
                List(opType),
                MakeTuple(inputAdd, inputValue),
                TupleGet(inputState, IntLit(2)),
            )
        )

        return Synth(name, summary, *ci.modifiedVars, *ci.readVars)


def initState():
    return MakeTuple(
        *[elem[2] for elem in synthStateStructure],
        Call("list_empty", List(opType))
    )

def targetLang():
    def list_length(l):
        return Call("list_length", Int(), l)

    def list_empty():
        return Call("list_empty", List(opType))

    def list_get(l, i):
        return Call("list_get", opType, l, i)

    def list_tail(l, i):
        return Call("list_tail", List(opType), l, i)

    data = Var("data", List(opType))
    next_state_fn = Var("next_state_fn", Fn(synthStateType, synthStateType, *opType.args))

    reduce_fn = FnDecl(
        "apply_state_transitions",
        synthStateType,
        Ite(
            Eq(list_length(data), IntLit(0)),
            initState(),
            Call(
                "next_state_fn",
                # TODO(shadaj): this is a bogus hack
                Fn(synthStateType, synthStateType, *opType.args),
                # synthStateType,
                Call("apply_state_transitions", synthStateType, list_tail(data, IntLit(1)), next_state_fn),
                *[
                    TupleGet(list_get(data, IntLit(0)), IntLit(i))
                    for i in range(len(opType.args))
                ]
            ),
        ),
        data,
        next_state_fn,
    )

    next_op = Var("next_op", opType)
    ops_in_order_helper = FnDecl(
        "ops_in_order_helper",
        Bool(),
        Ite(
            Eq(list_length(data), IntLit(0)),
            BoolLit(True),
            And(
                inOrder(unpackOp(list_get(data, IntLit(0))), unpackOp(next_op)),
                Call("ops_in_order_helper", Bool(), list_get(data, IntLit(0)), list_tail(data, IntLit(1))),
            )
        ),
        next_op,
        data
    )

    ops_in_order = FnDecl(
        "ops_in_order",
        Bool(),
        Ite(
            Eq(list_length(data), IntLit(0)),
            BoolLit(True),
            Call("ops_in_order_helper", Bool(), list_get(data, IntLit(0)), list_tail(data, IntLit(1))),
        ),
        data
    )

    return [reduce_fn, ops_in_order_helper, ops_in_order]


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
        if mode == "synth-debug":
            fastDebug = True

        synthesize_actor(
            filename,
            fnNameBase,
            loopsFile,
            cvcPath,
            synthStateType,
            opType,
            initState,
            grammarStateInvariant,
            grammarSupportedCommand,
            inOrder,
            grammar,
            grammarQuery,
            grammarEquivalence,
            targetLang,
            synthesize,
            useOpList=True
        )
