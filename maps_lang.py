from ir import *
import typing


def mapsLang() -> typing.List[Expr]:
    def list_length(l: Expr) -> Expr:
        return Call("list_length", Int(), l)

    def list_get(l: Expr, i: Expr) -> Expr:
        return Call("list_get", Int(), l, i)

    def list_tail(l: Expr, i: Expr) -> Expr:
        return Call("list_tail", List(Int()), l, i)

    data = Var("data", List(Int()))
    lr_fn = Var("f", Fn(Int(), Int(), Int()))
    initial = Var("initial", Int())
    reduce_fn = FnDecl(
        "reduce",
        Int(),
        Ite(
            Eq(list_length(data), IntLit(0)),
            initial,
            CallValue(
                lr_fn,
                list_get(data, IntLit(0)),
                Call("reduce", Int(), list_tail(data, IntLit(1)), lr_fn, initial),
            ),
        ),
        data,
        lr_fn,
        initial,
    )

    # m1 = Var("m1", Map(Int(), Int()))
    # m2 = Var("m2", Map(Int(), Int()))
    # k = Var("k", Int())
    # union_fn = FnDefine(
    #     "map_union",
    #     Map(Int(), Int()),
    #     m1,
    #     m2
    # )

    # union_axiom_1 = Axiom(
    #     Implies(Or(
    #         Call("map_contains", Bool(), m1, k),
    #         Call("map_contains", Bool(), m2, k)
    #     ), Call("map_contains", Bool(), Call("map_union", Map(Int(), Int()), m1, m2), k)),
    #     m1, m2, k
    # )

    # union_axiom_2 = Axiom(
    #     Implies(And(
    #         Call("map_contains", Bool(), m1, k),
    #         Call("map_contains", Bool(), m2, k)
    #     ), Eq(
    #         synthStateStructure[0].valueType.merge(
    #             Call("map_get_direct", Int(), m1, k),
    #             Call("map_get_direct", Int(), m2, k)
    #         ),
    #         Call("map_get_direct", Int(), Call("map_union", Map(Int(), Int()), m1, m2), k))
    #     ),
    #     m1, m2, k
    # )

    # union_axiom_3 = Axiom(
    #     Implies(And(
    #         Call("map_contains", Bool(), m1, k),
    #         Not(Call("map_contains", Bool(), m2, k))
    #     ), Eq(
    #         Call("map_get_direct", Int(), m1, k),
    #         Call("map_get_direct", Int(), Call("map_union", Map(Int(), Int()), m1, m2), k))
    #     ),
    #     m1, m2, k
    # )

    # union_axiom_4 = Axiom(
    #     Implies(And(
    #         Not(Call("map_contains", Bool(), m1, k)),
    #         Call("map_contains", Bool(), m2, k)
    #     ), Eq(
    #         Call("map_get_direct", Int(), m2, k),
    #         Call("map_get_direct", Int(), Call("map_union", Map(Int(), Int()), m1, m2), k))
    #     ),
    #     m1, m2, k
    # )

    return [
        reduce_fn,
        # union_fn,
        # union_axiom_1,
        # union_axiom_2,
        # union_axiom_3,
        # union_axiom_4,
    ]
