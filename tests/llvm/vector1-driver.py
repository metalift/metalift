from typing import List, Union

from mypy.nodes import Statement

from metalift.frontend.llvm import Driver
from metalift.ir import And, Bool, BoolLit, Call, Choose, Eq, Expr, FnDecl,FnDeclRecursive, Ge, Gt, Int, IntLit, Ite, Le, ListT, Lt, Var
from tests.python.utils.utils import codegen


def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    arg = Var("n", Int())
    select_pred = FnDecl("Select-pred", Bool(), Gt(arg, IntLit(2)), arg)
    select_pred1 = FnDecl("Select-pred1", Bool(), Lt(arg, IntLit(10)), arg)
    select_pred2 = FnDecl("Select-pred2", Bool(), And(Gt(arg, IntLit(2)), Lt(arg, IntLit(10))), arg)

    data = Var("l", ListT(Int()))
    select_func = FnDeclRecursive(
        "Select",
        ListT(Int()),
        Ite(
            Eq(Call("list_length", Int(), data), IntLit(0)),
            Call("list_empty", ListT(Int())),
            Ite(
                Call("Select-pred", Bool(), Call("list_get", Int(), data, IntLit(0))),
                Call(
                    "list_append",
                    ListT(Int()),
                    Call(
                        "Select",
                        ListT(Int()),
                        Call("list_tail", ListT(Int()), data, IntLit(1)),
                    ),
                    Call("list_get", Int(), data, IntLit(0)),
                ),
                Call(
                    "Select",
                    ListT(Int()),
                    Call("list_tail", ListT(Int()), data, IntLit(1)),
                ),
            ),
        ),
        data,
    )
    select_func1 = FnDeclRecursive(
        "Select1",
        ListT(Int()),
        Ite(
            Eq(Call("list_length", Int(), data), IntLit(0)),
            Call("list_empty", ListT(Int())),
            Ite(
                Call("Select-pred1", Bool(), Call("list_get", Int(), data, IntLit(0))),
                Call(
                    "list_append",
                    ListT(Int()),
                    Call(
                        "Select1",
                        ListT(Int()),
                        Call("list_tail", ListT(Int()), data, IntLit(1)),
                    ),
                    Call("list_get", Int(), data, IntLit(0)),
                ),
                Call(
                    "Select1",
                    ListT(Int()),
                    Call("list_tail", ListT(Int()), data, IntLit(1)),
                ),
            ),
        ),
        data,
    )
    select_func2 = FnDeclRecursive(
        "Select2",
        ListT(Int()),
        Ite(
            Eq(Call("list_length", Int(), data), IntLit(0)),
            Call("list_empty", ListT(Int())),
            Ite(
                Call("Select-pred2", Bool(), Call("list_get", Int(), data, IntLit(0))),
                Call(
                    "list_append",
                    ListT(Int()),
                    Call(
                        "Select2",
                        ListT(Int()),
                        Call("list_tail", ListT(Int()), data, IntLit(1)),
                    ),
                    Call("list_get", Int(), data, IntLit(0)),
                ),
                Call(
                    "Select2",
                    ListT(Int()),
                    Call("list_tail", ListT(Int()), data, IntLit(1)),
                ),
            ),
        ),
        data,
    )

    return [
        select_pred,
        select_pred1,
        select_pred2,
        select_func,
        select_func1,
        select_func2,
    ]

def ps_grammar(ret_val: Var, writes: List[Var], reads: List[Var]) -> Expr:
    # reads = [in_lst]
    return Choose(
        Call("list_eq", Bool(), ret_val, *reads),
        Call("list_eq", Bool(), ret_val, Call("Select", ListT(Int()), *reads)),
        Call("list_eq", Bool(), ret_val, Call("Select1", ListT(Int()), *reads)),
        Call("list_eq", Bool(), ret_val, Call("Select2", ListT(Int()), *reads))
    )

def inv_grammar(v: Var, writes: List[Var], reads: List[Var]) -> Expr:
    # This grammar func could be called with v as `i` or `out_lst`, and we really only want to generate this grammar once.
    if v.name() != "out_lst":
        return BoolLit(True)

    # writes = [i, out_lst]
    # reads = [i, in_lst, out_lst]
    i, out_lst = writes[0], writes[1]
    in_lst = reads[1]
    lst = Choose(in_lst, out_lst, Call("Select", ListT(Int()), in_lst))
    lst_inv_cond = Choose(
        Call(
            "list_eq",
            Bool(),
            Call(
                "list_append",
                ListT(Int()),
                lst,
                Call(
                    "Select",
                    ListT(Int()),
                    Call("list_tail", ListT(Int()), lst, i),
                ),
            ),
            lst,
        ),
        Call(
            "list_eq",
            Bool(),
            Call(
                "list_concat",
                ListT(Int()),
                writes[1],
                Call("list_tail", ListT(Int()), lst, i),
            ),
            lst,
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
    return Choose(And(And(i_bound_int_lit_cond, i_bound_in_lst_length_cond), lst_inv_cond))

if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        "tests/llvm/vector1.ll",
        "tests/llvm/vector1.loops",
        "test",
        target_lang,
        inv_grammar,
        ps_grammar
    )

    in_var = driver.variable("in", ListT(Int()))

    test(in_var)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))