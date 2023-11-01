from typing import List

from mypy.nodes import Statement

from metalift.frontend.python import Driver
from metalift.ir import *
from tests.python.utils.utils import codegen

fn_ret_bool_type = FnT(BoolObject)

def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    arg = IntObject("n")
    select_pred = FnDecl("Select-pred", fn_ret_bool_type, arg > 2, arg)
    select_pred1 = FnDecl("Select-pred1", fn_ret_bool_type, arg < 10, arg)
    select_pred2 = FnDecl(
        "Select-pred2",
        fn_ret_bool_type,
        arg > 2 and arg < 10,
        arg
    )
    data = ListObject(IntObject, "l")
    f = NewObject("f", fn_ret_bool_type)
    select_func = FnDeclRecursive(
        "Select",
        ListObject[IntObject],
        Ite(
            Eq(Call("list_length", IntObject, data), IntObject(0)),
            ListObject.empty(IntObject),
            Ite(
                CallValue(f, data[0]),
                Call(
                    "list_append",
                    ListObject[IntObject],
                    Call(
                        "Select",
                        ListObject[IntObject],
                        Call("list_tail", ListObject[IntObject], data, IntObject(1)),
                        f,
                    ),
                    data[0],
                ),
                Call(
                    "Select",
                    ListObject[IntObject],
                    Call("list_tail", ListObject[IntObject], data, IntObject(1)),
                    f,
                ),
            ),
        ),
        data,
        f,
    )

    return [select_pred, select_pred1, select_pred2, select_func]

def inv_grammar(
    v: NewObject, writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]
) -> Expr:
    # This grammar func could be called with v as `i` or `out_lst`, and we really only want to generate this grammar once.
    if v.var_name() != "out_lst":
        return BoolObject(True)

    # writes = [i, out_lst]
    # reads = [i, in_lst, out_lst]
    i, out_lst = writes[0], writes[1]
    in_lst = reads[1]
    f = Choose(
        Call("Select-pred", fn_ret_bool_type),
        Call("Select-pred1", fn_ret_bool_type),
        Call("Select-pred2", fn_ret_bool_type),
    )
    lst = Choose(in_lst, out_lst, Call("Select", ListObject[IntObject], in_lst, f))
    i_bound_int_lit = Choose(IntObject(0), IntObject(1))
    lst_inv_cond = Choose(
        Call(
            "list_eq",
            BoolObject,
            Call(
                "list_concat",
                ListObject[IntObject],
                lst,
                Call(
                    "Select",
                    ListObject[IntObject],
                    Call("list_tail", ListObject[IntObject], lst, i),
                    f,
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
                lst,
                Call("list_tail", ListObject[IntObject], lst, i),
            ),
            lst,
        ),
    )
    in_lst_length = in_lst.len()
    i_bound_in_lst_length_cond = Choose(
        Ge(i, in_lst_length),
        Le(i, in_lst_length),
        Gt(i, in_lst_length),
        Lt(i, in_lst_length),
        Eq(i, in_lst_length),
    )
    i_bound_int_lit_cond = Choose(
        Ge(i, i_bound_int_lit),
        Le(i, i_bound_int_lit),
        Gt(i, i_bound_int_lit),
        Lt(i, i_bound_int_lit),
        Eq(i, i_bound_int_lit),
    )
    return Choose(And(And(i_bound_int_lit_cond, i_bound_in_lst_length_cond), lst_inv_cond))

def ps_grammar(ret_val: NewObject, writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> Expr:
    # reads = [in_lst]
    in_lst = reads[0]
    fns = Choose(
        Call("Select-pred", fn_ret_bool_type),
        Call("Select-pred1", fn_ret_bool_type),
        Call("Select-pred2", fn_ret_bool_type),
    )
    return Choose(
        Call("list_eq", BoolObject, ret_val, in_lst),
        Call(
            "list_eq",
            BoolObject,
            ret_val,
            Call("Select", ListObject[IntObject], in_lst, fns),
        )
    )


if __name__ == "__main__":
    filename = "tests/python/list1.py"

    driver = Driver()
    test = driver.analyze(filename, "test", target_lang, inv_grammar, ps_grammar)

    in_lst = ListObject[IntObject](IntObject, "in_lst")
    driver.add_var_object(in_lst)

    test(in_lst)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))

