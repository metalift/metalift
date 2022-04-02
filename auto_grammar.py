from ir import *

import typing
from typing import Union, Dict
from llvmlite.binding import ValueRef

equality_supported_types = [Bool(), Int(), ClockInt(), EnumInt(), OpaqueInt()]
comparison_supported_types = [Int, ClockInt()]


def get_expansions(
    input_types: typing.List[Type],
    available_types: typing.List[Type],
    out_types: typing.List[Type],
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
                (lambda t: lambda get: Gt(get(t), get(t)))(t)
                for t in comparison_supported_types
            ],
            *[
                (lambda t: lambda get: Ge(get(t), get(t)))(t)
                for t in comparison_supported_types
            ],
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
        if t in input_types:
            gen_set_ops(t)
        else:
            out[Set(t)] = []

        if Set(t) in out_types:
            out[Set(t)] += [
                (lambda t: lambda get: Call("set-create", Set(t)))(t),
                (lambda t: lambda get: Call("set-singleton", Set(t), get(t)))(t),
            ]

    def gen_map_ops(k: Type, v: Type) -> None:
        if Map(k, v) in out_types:
            out[Map(k, v)] = [
                lambda get: Call("map-create", Map(k, v)),
                lambda get: Call("map-singleton", Map(k, v), get(k), get(v)),
            ]

        if v not in out:
            out[v] = []

        if Map(k, v) in input_types:
            out[v] += [
                lambda get: Call("map-get", v, get(Map(k, v)), get(k), get(v)),
            ]

    for t in available_types:
        if t.name == "Map":
            gen_map_ops(t.args[0], t.args[1])

    if EnumInt() in available_types:
        if EnumInt() not in out:
            out[EnumInt()] = []
        out[EnumInt()] += [(lambda i: lambda get: EnumIntLit(i))(i) for i in range(4)]

    if ClockInt() in available_types:
        if ClockInt() not in out:
            out[ClockInt()] = []
        out[ClockInt()] += [lambda get: Lit(0, ClockInt())]

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

    def extract_inputs(input_type: Type, input: typing.Optional[Expr]) -> None:
        if input_type.name == "Tuple":
            for i, t in enumerate(input_type.args):
                if input != None:
                    extract_inputs(t, TupleGet(input, IntLit(i)))  # type: ignore
                else:
                    extract_inputs(t, None)
        else:
            if not input_type in input_pool:
                input_pool[input_type] = []
            if input != None:
                input_pool[input_type].append(input)  # type: ignore
            if input_type.name == "Set":
                extract_inputs(input_type.args[0], None)
            elif input_type.name == "Map":
                extract_inputs(input_type.args[0], None)
                extract_inputs(input_type.args[1], None)

    for input in inputs:
        input_type = parseTypeRef(input.type)
        extract_inputs(input_type, input)

    input_types = list(input_pool.keys())

    if out_type not in input_pool:
        extract_inputs(out_type, None)

    out_types = list(set(input_pool.keys()) - set(input_types))

    expansions = get_expansions(input_types, list(input_pool.keys()), out_types)

    pool: Dict[Type, Expr] = {}
    for t, exprs in input_pool.items():
        zero_input_expansions = []
        if t in expansions:
            for e in expansions[t]:
                try:
                    zero_input_expansions.append(e(lambda t: dict()[t]))  # type: ignore
                except KeyError:
                    pass
        if (len(exprs) + len(zero_input_expansions)) > 0:
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
