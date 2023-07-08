from typing import List, Tuple, Union
from metalift.frontend.python import Driver

from metalift.ir import Add, And, Axiom, BoolLit, Call, CallValue, Choose, Eq, Expr, FnDecl, FnDeclRecursive, FnT, Ge, Gt, Implies, Int, IntLit, Ite, Le, ListT, Lit, Lt, Mul, Sub, Synth, Var

from mypy.nodes import Statement, WhileStmt

from tests.python.utils.utils import codegen

# We need to define some global variables as they need to persist across function calls
LM_NAME = "lm"
LR_NAME = "lr"
arg2 = Var("val", Int())
arg3 = Var("val2", Int())

def fns_synths() -> List[Synth]:
    lm_synth = Synth(
        LM_NAME,
        Choose(IntLit(0), IntLit(1), IntLit(2), IntLit(3)),
        arg2
    )
    v = Choose(arg2, arg3)
    lr_synth = Synth(
        LR_NAME,
        Choose(Add(v, v), Sub(v, v), Mul(v, v)),
        arg2,
        arg3
    )
    return [lm_synth, lr_synth]

def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    def list_length(l):
        return Call("list_length", Int(), l)

    def list_empty():
        return Call("list_empty", ListT(Int()))

    def list_get(l, i):
        return Call("list_get", Int(), l, i)

    def list_tail(l, i):
        return Call("list_tail", ListT(Int()), l, i)

    data = Var("data", ListT(Int()))


    lm_fn = Var("f", FnT(Int(), Int()))
    lr_fn = Var("f", FnT(Int(), Int(), Int()))

    mapper = FnDecl(LM_NAME, Int(), None, arg2)
    reducer = FnDecl(LR_NAME, Int(), None, arg2, arg3)
    # if len(data) == 0:
    #     return []
    # else:
    #     return list_prepend(lm_fn(data[0]), map(list_tail(data, 1), lm_fn))
    map_fn = FnDeclRecursive(
        "map",
        ListT(Int()),
        Ite(
            Eq(list_length(data), IntLit(0)),
            list_empty(),
            Call(
                "list_prepend",
                ListT(Int()),
                CallValue(lm_fn, list_get(data, IntLit(0))),
                Call("map", ListT(Int()), list_tail(data, IntLit(1)), lm_fn),
            ),
        ),
        data,
        lm_fn,
    )

    # if len(data) == 0:
    #     return 0
    # else:
    #     return lr_fn(data[0], reduce(list_tail(data, 1)), lr_fn)
    reduce_fn = FnDeclRecursive(
        "reduce",
        Int(),
        Ite(
            Eq(list_length(data), IntLit(0)),
            IntLit(0),
            CallValue(
                lr_fn,
                list_get(data, IntLit(0)),
                Call("reduce", Int(), list_tail(data, IntLit(1)), lr_fn),
            ),
        ),
        data,
        lr_fn,
    )

    mr_axiom_data = Var("data", ListT(Int()))
    mr_axiom_index = Var("index", Int())
    map_reduce_axiom = Axiom(
        Implies(
            And(Ge(mr_axiom_index, IntLit(0)), Lt(mr_axiom_index, list_length(mr_axiom_data))),
            Eq(
                Call(
                    "reduce",
                    Int(),
                    Call(
                        "map",
                        ListT(Int()),
                        Call(
                            "list_take",
                            ListT(Int()),
                            mr_axiom_data,
                            Add(mr_axiom_index, IntLit(1))
                        ),
                        Var(LM_NAME, FnT(Int(), Int()))
                    ),
                    Var(LR_NAME, FnT(Int(), Int(), Int())),
                ),
                Call(
                    LR_NAME,
                    Int(),
                    Call(
                        "reduce",
                        Int(),
                        Call(
                            "map",
                            ListT(Int()),
                            Call(
                                "list_take",
                                ListT(Int()),
                                mr_axiom_data,
                                mr_axiom_index
                            ),
                            Var(LM_NAME, FnT(Int(), Int()))
                        ),
                        Var(LR_NAME, FnT(Int(), Int(), Int())),
                    ),
                    Call(
                        LM_NAME,
                        Int(),
                        Call(
                            "list_get",
                            Int(),
                            mr_axiom_data,
                            mr_axiom_index
                        )
                    ),
                ),
            ),
        ),
        mr_axiom_data,
        mr_axiom_index,
    )

    return [map_fn, reduce_fn, map_reduce_axiom, mapper, reducer]


# var := *reads | 0
# added := var + var
# var_or_fma := *reads | fma(added, added, added)
#
# return value := var_or_fma + var_or_fma
#
def ps_grammar(ret_val: Var, ast: Statement, writes: List[Var], reads: List[Var], in_scope: List[Var]) -> Expr:
    # reads = [in_lst]
    in_lst = reads[0]
    choices = Choose(
        Eq(
            ret_val,
            Call(
                "reduce",
                Int(),
                Call("map", ListT(Int()), in_lst, Var(LM_NAME, FnT(Int(), Int()))),
                Var(LR_NAME, FnT(Int(), Int(), Int())),
            ),
        ),
        Gt(
            ret_val,
            Call(
                "reduce",
                Int(),
                Call("map", ListT(Int()), in_lst, Var(LM_NAME, FnT(Int(), Int()))),
                Var(LR_NAME, FnT(Int(), Int(), Int())),
            ),
        ),
    )
    return choices

def inv_grammar(v: Var, ast: Statement, writes: List[Var], reads: List[Var], in_scope: List[Var]) -> Expr:
    if v.name() != "count":
        return BoolLit(True)

    # writes = [count, i]
    # reads = [count, i, in_lst]
    count, i = writes
    in_lst = reads[2]

    count_inv_cond = Choose(
        Eq(
            count,
            Call(
                "reduce",
                Int(),
                Call(
                    "map",
                    ListT(Int()),
                    Call(
                        "list_take", ListT(Int()), in_lst, i
                    ),
                    Var(LM_NAME, FnT(Int(), Int())),
                ),
                Var(LR_NAME, FnT(Int(), Int(), Int())),
            ),
        ),
        Ge(
            count,
            Call(
                "reduce",
                Int(),
                Call(
                    "map",
                    ListT(Int()),
                    Call(
                        "list_take", ListT(Int()), in_lst, i
                    ),
                    Var(LM_NAME, FnT(Int(), Int())),
                ),
                Var(LR_NAME, FnT(Int(), Int(), Int())),
            ),
        ),
    )
    in_lst_length = Call("list_length", Int(), in_lst)
    i_bound_in_lst_length_cond = Choose(
        Ge(i, in_lst_length),
        Le(i, in_lst_length),
        Gt(i, in_lst_length),
        Lt(i, in_lst_length),
        Eq(i, in_lst_length),
    )
    i_bound_int_lit = Choose(IntLit(0), IntLit(1))
    i_bound_int_lit_cond = Choose(
        Ge(i, i_bound_int_lit),
        Le(i, i_bound_int_lit),
        Gt(i, i_bound_int_lit),
        Lt(i, i_bound_int_lit),
        Eq(i, i_bound_int_lit),
    )
    return Choose(And(And(i_bound_in_lst_length_cond, i_bound_int_lit_cond), count_inv_cond))

if __name__ == "__main__":
    filename = "tests/python/count.py"

    driver = Driver()
    driver.fns_synths = fns_synths()
    test = driver.analyze(filename, "test", target_lang, inv_grammar, ps_grammar)

    v1 = driver.variable("data", ListT(Int()))

    test(v1)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))
