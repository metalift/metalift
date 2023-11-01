from typing import List, Union

from metalift.frontend.python import Driver
from metalift.ir import (And, Call, Choose, Eq, Expr, FnDecl,FnDeclRecursive, Ge, Gt, Ite, Le, Lt, NewObject,
    ListObject, IntObject, BoolObject, ite)
from tests.python.utils.utils import codegen

def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    arg = IntObject("n")
    select_pred = FnDecl("Select-pred", BoolObject, arg > 2, arg)
    select_pred1 = FnDecl("Select-pred1", BoolObject, arg < 10, arg)
    select_pred2 = FnDecl(
        "Select-pred2",
        BoolObject,
        arg > 2 and arg < 10,
        arg
    )

    data = ListObject(IntObject, "l")
    select_func = FnDeclRecursive(
        "Select",
        ListObject[IntObject],
        ite(
            data.len() == 0,
            ListObject.empty(IntObject),
            Ite(
                Call("Select-pred", BoolObject, data[0]),
                Call(
                    "list_append",
                    ListObject[IntObject],
                    Call(
                        "Select",
                        ListObject[IntObject],
                        data[1:],
                    ),
                    data[0],
                ),
                Call(
                    "Select",
                    ListObject[IntObject],
                    data[1:],
                ),
            ),
        ),
        data,
    )
    select_func1 = fn_decl_recursive(
        "Select1",
        ListObject[IntObject],
        ite(
            data.len() == IntObject(0),
            ListObject.empty(IntObject),
            Ite(
                Call("Select-pred1", BoolObject, data[0]),
                Call(
                    "list_append",
                    ListObject[IntObject],
                    Call(
                        "Select1",
                        ListObject[IntObject],
                        data[1:],
                    ),
                    data[0],
                ),
                Call(
                    "Select1",
                    ListObject[IntObject],
                    data[1:],
                ),
            ),
        ),
        data,
    )
    select_func2 = fn_decl_recursive(
        "Select2",
        ListObject[IntObject],
        ite(
            data.len() == IntObject(0),
            ListObject.empty(IntObject),
            Ite(
                Call("Select-pred2", BoolObject, data[0]),
                Call(
                    "list_append",
                    ListObject[IntObject],
                    Call(
                        "Select2",
                        ListObject[IntObject],
                        data[1:],
                    ),
                    data[0],
                ),
                Call(
                    "Select2",
                    ListObject[IntObject],
                    data[1:],
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

def ps_grammar(ret_val: NewObject, writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> Expr:
    # reads = [in_lst]
    return Choose(
        Call("list_eq", BoolObject, ret_val, *reads),
        Call("list_eq", BoolObject, ret_val, Call("Select", ListObject[IntObject], *reads)),
        Call("list_eq", BoolObject, ret_val, Call("Select1", ListObject[IntObject], *reads)),
        Call("list_eq", BoolObject, ret_val, Call("Select2", ListObject[IntObject], *reads))
    )

def inv_grammar(v: NewObject, writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> Expr:
    # This grammar func could be called with v as `i` or `out_lst`, and we really only want to generate this grammar once.
    if v.var_name() != "out_lst":
        return BoolObject(True)

    # writes = [i, out_lst]
    # reads = [i, in_lst, out_lst]
    i, out_lst = writes[0], writes[1]
    in_lst = reads[1]
    lst = Choose(in_lst, out_lst, Call("Select", ListObject[IntObject], in_lst))
    lst_inv_cond = Choose(
        Call(
            "list_eq",
            BoolObject,
            Call(
                "list_append",
                ListObject[IntObject],
                lst,
                Call(
                    "Select",
                    ListObject[IntObject],
                    Call("list_tail", ListObject[IntObject], lst, i),
                ),
            ),
            lst,
        ),
        Call(
            "list_eq",
            BoolObject,
            Call(
                "list_concat",
                ListObject[IntObject],
                out_lst,
                Call("list_tail", ListObject[IntObject], lst, i),
            ),
            lst,
        ),
    )

    in_lst_length = in_lst.len()
    i_bound_in_lst_length_cond = Choose(
        i >= in_lst_length,
        i <= in_lst_length,
        i > in_lst_length,
        i < in_lst_length,
        i == in_lst_length,
    )
    i_bound_int_lit = Choose(IntObject(0), IntObject(1))
    i_bound_int_lit_cond = Choose(
        Ge(i, i_bound_int_lit),
        Le(i, i_bound_int_lit),
        Gt(i, i_bound_int_lit),
        Lt(i, i_bound_int_lit),
        Eq(i, i_bound_int_lit),
    )
    return choose(and_objects(i_bound_int_lit_cond, i_bound_in_lst_length_cond, lst_inv_cond))


if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        filepath="tests/python/list1.py",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammar=inv_grammar,
        ps_grammar=ps_grammar
    )

    in_lst = ListObject(IntObject, "in_lst")
    driver.add_var_object(in_lst)

    test(in_lst)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))
