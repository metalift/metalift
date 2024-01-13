from typing import List, Union

from metalift.frontend.python import Driver
from metalift.ir import Bool, Expr, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, call, choose, fn_decl, fn_decl_recursive, ite
from metalift.vc_util import and_objects
from tests.python.utils.utils import codegen


def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    arg = Int("n")
    select_pred = fn_decl("Select-pred", Bool, (arg > 2), arg)
    select_pred1 = fn_decl("Select-pred1", Bool, (arg < 10), arg)
    select_pred2 = fn_decl("Select-pred2", Bool, (arg > 2) and (arg < 10), arg)

    data = mlList(Int, "l")
    select_func = fn_decl_recursive(
        "Select",
        mlList[Int],
        ite(
            data.len() == 0,
            mlList.empty(Int),
            ite(
                call("Select-pred", Bool, data[0]),
                call("Select", mlList[Int], data[1:]).append(data[0]),
                call("Select", mlList[Int], data[1:]),
            ),
        ),
        data,
    )
    select_func1 = fn_decl_recursive(
        "Select1",
        mlList[Int],
        ite(
            data.len() == 0,
            mlList.empty(Int),
            ite(
                call("Select-pred1", Bool, data[0]),
                call("Select1", mlList[Int], data[1:]).append(data[0]),
                call("Select1", mlList[Int], data[1:]),
            ),
        ),
        data,
    )
    select_func2 = fn_decl_recursive(
        "Select2",
        mlList[Int],
        ite(
            data.len() == 0,
            mlList.empty(Int),
            ite(
                call("Select-pred2", Bool, data[0]),
                call("Select2", mlList[Int], data[1:]).append(data[0]),
                call("Select2", mlList[Int], data[1:]),
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


def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Expr:
    # reads = [in_lst]
    ret_val = writes[0]
    in_lst = reads[0]
    return choose(
        ret_val == in_lst,
        ret_val == call("Select", mlList[Int], in_lst),
        ret_val == call("Select1", mlList[Int], in_lst),
        ret_val == call("Select2", mlList[Int], in_lst),
    )


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Expr:
    i, out_lst = writes[0], writes[1]
    in_lst = reads[1]
    lst = choose(in_lst, out_lst, call("Select", mlList[Int], in_lst))
    lst_inv_cond = choose(
        lst + call("Select", mlList[Int], lst[i:]) == lst, out_lst + lst[i:] == lst
    )

    in_lst_length = in_lst.len()
    i_bound_in_lst_length_cond = choose(
        i >= in_lst_length,
        i <= in_lst_length,
        i > in_lst_length,
        i < in_lst_length,
        i == in_lst_length,
    )
    i_bound_int_lit = choose(Int(0), Int(1))
    i_bound_int_lit_cond = choose(
        i >= i_bound_int_lit,
        i <= i_bound_int_lit,
        i > i_bound_int_lit,
        i < i_bound_int_lit,
        i == i_bound_int_lit,
    )
    return choose(
        and_objects(i_bound_int_lit_cond, i_bound_in_lst_length_cond, lst_inv_cond)
    )


if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        filepath="tests/python/list1.py",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammar=inv_grammar,
        ps_grammar=ps_grammar,
    )

    in_lst = mlList(Int, "in_lst")
    driver.add_var_object(in_lst)

    test(in_lst)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))
