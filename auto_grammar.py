from ir import *

import typing
from typing import Union, Dict
from llvmlite.binding import ValueRef


def get_expansions(
    enable_sets: bool = False,
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
            lambda get: And(get(Bool()), get(Bool())),
            lambda get: Or(get(Bool()), get(Bool())),
            lambda get: Not(get(Bool())),
            lambda get: Eq(get(Int()), get(Int())),
            lambda get: Lt(get(Int()), get(Int())),
            lambda get: Gt(get(Int()), get(Int())),
            # lambda get: Le(get(Int()), get(Int())),
            # lambda get: Ge(get(Int()), get(Int())),
        ],
    }

    if enable_sets:
        out[Set(Int())] = [
            lambda get: Call("set-minus", Set(Int()), get(Set(Int())), get(Set(Int()))),
            lambda get: Call("set-union", Set(Int()), get(Set(Int())), get(Set(Int()))),
            lambda get: Call("set-singleton", Set(Int()), get(Int())),
            lambda get: Call("set-insert", Set(Int()), get(Int()), get(Set(Int()))),
        ]

        out[Bool()].append(lambda get: Eq(get(Set(Int())), get(Set(Int()))))
        out[Bool()].append(
            lambda get: Call("set-subset", Bool(), get(Set(Int())), get(Set(Int())))
        )
        out[Bool()].append(
            lambda get: Call("set-member", Bool(), get(Int()), get(Set(Int())))
        )

    return out


def auto_grammar(
    out_type: Type,
    depth: int,
    *inputs: Union[Expr, ValueRef],
    enable_sets: bool = False,
    enable_ite: bool = False,
) -> Expr:
    expansions = get_expansions(enable_sets)

    pool = {}

    if enable_sets:
        pool[Set(Int())] = Call("set-create", Set(Int()))

    input_pool: Dict[Type, typing.List[Expr]] = {}
    for input in inputs:
        input_type = parseTypeRef(input.type)
        if input_type.name == "Tuple":
            for i, t in enumerate(input_type.args):
                if not t in input_pool:
                    input_pool[t] = []
                input_pool[t].append(TupleGet(input, IntLit(i)))
        else:
            if not input_type in input_pool:
                input_pool[input_type] = []
            input_pool[input_type].append(input)

    for t, exprs in input_pool.items():
        if t in pool:
            pool[t] = Choose(pool[t], Choose(*exprs))
        else:
            pool[t] = Choose(*exprs)

    at_depth = {
        0: pool,
    }

    for i in range(depth):
        next_pool = {}
        for t, expansion_list in expansions.items():
            new_elements = []
            for expansion in expansion_list:
                try:
                    new_elements.append(expansion(lambda t: pool[t]))
                except KeyError:
                    pass

            if enable_ite and Bool() in pool and t in pool:
                new_elements.append(Ite(pool[Bool()], pool[t], pool[t]))

            if len(new_elements) > 0:
                if t in pool:
                    next_pool[t] = Choose(pool[t], *new_elements)
                else:
                    next_pool[t] = Choose(*new_elements)

        for t in pool.keys():
            if not (t in next_pool):
                if enable_ite and Bool() in pool:
                    next_pool[t] = Choose(pool[t], Ite(pool[Bool()], pool[t], pool[t]))
                else:
                    next_pool[t] = pool[t]

        at_depth[i + 1] = next_pool
        pool = next_pool

    return Choose(*[p[out_type] for p in at_depth.values() if out_type in p])
