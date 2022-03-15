from ir import *

import typing
from typing import Union, Dict
from llvmlite.binding import ValueRef

equality_supported_types = [Int(), ClockInt(), EnumInt(), OpaqueInt()]
comparison_supported_types = [Int, ClockInt()]


def get_expansions() -> Dict[
    Type, typing.List[typing.Callable[[typing.Callable[[Type], Expr]], Expr]]
]:
    out: Dict[
        Type, typing.List[typing.Callable[[typing.Callable[[Type], Expr]], Expr]]
    ] = {
        Int(): [
            lambda get: Add(get(Int()), get(Int())),
            lambda get: Sub(get(Int()), get(Int())),
            # lambda get: Mul(get(Int()), get(Int())),
        ],
        Bool(): [
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

    expansions = get_expansions()

    pool: Dict[Type, Expr] = {}

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

    if not Bool() in input_pool:
        input_pool[Bool()] = []
    input_pool[Bool()] += [BoolLit(False), BoolLit(True)]

    for t in equality_supported_types:
        if out_type == Set(t) and Set(t) not in input_pool:
            input_pool[Set(t)] = []
        if Set(t) in input_pool:
            input_pool[Set(t)] += [Call("set-create", Set(t))]
            expansions[Set(t)] += [(lambda t: lambda get: Call("set-singleton", Set(t), get(t)))(t)]

    if out_type == EnumInt() and EnumInt() not in input_pool:
        input_pool[EnumInt()] = []
    if EnumInt() in input_pool:
        input_pool[EnumInt()] += [EnumIntLit(i) for i in range(4)]

    for t, exprs in input_pool.items():
        if t in pool:
            pool[t] = Choose(pool[t], Choose(*exprs))
        else:
            pool[t] = Choose(*exprs)

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
