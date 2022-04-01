from ir import *

import typing
from typing import Union, Dict
from llvmlite.binding import ValueRef

equality_supported_types = [Bool(), Int(), ClockInt(), EnumInt(), OpaqueInt()]
comparison_supported_types = [Int, ClockInt()]


def get_expansions(
    input_types: typing.List[Type],
) -> Dict[Type, typing.List[typing.Callable[[typing.Callable[[Type], Expr]], Expr]]]:
    out: Dict[
        Type, typing.List[typing.Callable[[typing.Callable[[Type], Expr]], Expr]]
    ] = {
        Int(): [
            lambda get: Add(get(Int()), get(Int())),
            lambda get: Sub(get(Int()), get(Int())),
            # lambda get: Mul(get(Int()), get(Int())),
        ],
        Bool(): [
            lambda get: BoolLit(False),
            lambda get: BoolLit(True),
            lambda get: And(get(Bool()), get(Bool())),
            lambda get: Or(get(Bool()), get(Bool())),
            lambda get: Not(get(Bool())),
            *[
                (lambda t: lambda get: Eq(get(t), get(t)))(t)
                for t in equality_supported_types
            ],
            *[
                (lambda t: lambda get: Lt(get(t), get(t)))(t)
                for t in comparison_supported_types
            ],
            *[
                (lambda t: lambda get: Gt(get(t), get(t)))(t)
                for t in comparison_supported_types
            ],
            # lambda get: Le(get(Int()), get(Int())),
            # lambda get: Ge(get(Int()), get(Int())),
        ],
    }

    def gen_set_ops(t: Type) -> None:
        out[Set(t)] = [
            lambda get: Call("set-minus", Set(t), get(Set(t)), get(Set(t))),
            lambda get: Call("set-union", Set(t), get(Set(t)), get(Set(t))),
            lambda get: Call("set-insert", Set(t), get(t), get(Set(t))),
        ]

        out[Bool()].append(lambda get: Eq(get(Set(t)), get(Set(t))))
        out[Bool()].append(
            lambda get: Call("set-subset", Bool(), get(Set(t)), get(Set(t)))
        )
        out[Bool()].append(lambda get: Call("set-member", Bool(), get(t), get(Set(t))))

    for t in equality_supported_types:
        gen_set_ops(t)
        if Set(t) in input_types:
            out[Set(t)] += [
                (lambda t: lambda get: Call("set-create", Set(t)))(t),
                (lambda t: lambda get: Call("set-singleton", Set(t), get(t)))(t),
            ]

    if EnumInt() in input_types:
        out[EnumInt()] = [(lambda i: lambda get: EnumIntLit(i))(i) for i in range(4)]

    return out


def auto_grammar(
    out_type: Type,
    depth: int,
    *inputs: Union[Expr, ValueRef],
    enable_ite: bool = False,
) -> Expr:
    if out_type.name == "Tuple":
        return MakeTuple(
            *[
                auto_grammar(
                    t,
                    depth,
                    *inputs,
                    enable_ite=enable_ite,
                )
                for t in out_type.args
            ]
        )

    input_pool: Dict[Type, typing.List[Expr]] = {}

    def extract_inputs(input_type: Type, input: Expr) -> None:
        if input_type.name == "Tuple":
            for i, t in enumerate(input_type.args):
                extract_inputs(t, TupleGet(input, IntLit(i)))
        else:
            if not input_type in input_pool:
                input_pool[input_type] = []
            input_pool[input_type].append(input)

    for input in inputs:
        input_type = parseTypeRef(input.type)
        extract_inputs(input_type, input)

    if out_type not in input_pool:
        input_pool[out_type] = []

    expansions = get_expansions(list(input_pool.keys()))

    pool: Dict[Type, Expr] = {}
    for t, exprs in input_pool.items():
        zero_input_expansions = []
        if t in expansions:
            for e in expansions[t]:
                try:
                    zero_input_expansions.append(e(lambda t: dict()[t]))  # type: ignore
                except KeyError:
                    pass
        pool[t] = Choose(*exprs, *zero_input_expansions)

    for i in range(depth):
        next_pool = dict(pool)
        for t, expansion_list in expansions.items():
            new_elements = []
            for expansion in expansion_list:
                try:
                    new_elements.append(expansion(lambda t: pool[t]))
                except KeyError:
                    pass

            if t in pool:
                next_pool[t] = Choose(next_pool[t], *new_elements)
            elif len(new_elements) > 0:
                next_pool[t] = Choose(*new_elements)

        if enable_ite and Bool() in pool:
            for t in pool.keys():
                next_pool[t] = Choose(next_pool[t], Ite(pool[Bool()], pool[t], pool[t]))

        pool = next_pool

    return pool[out_type]
