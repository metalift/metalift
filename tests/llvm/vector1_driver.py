from collections import defaultdict
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import BoolObject, FnDecl, FnDeclRecursive, IntObject, ListObject, NewObject, call, choose, ite, fn_decl, fn_decl_recursive
from metalift.vc_util import and_objects
from tests.python.utils.utils import codegen


def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    arg = IntObject("n")
    select_pred = fn_decl("Select-pred", BoolObject, (arg > 2), arg)
    select_pred1 = fn_decl("Select-pred1", BoolObject, (arg < 10), arg)
    select_pred2 = fn_decl("Select-pred2", BoolObject, (arg > 2) and (arg < 10), arg)

    data = ListObject(IntObject, "l")
    select_func = fn_decl_recursive(
        "Select",
        ListObject[IntObject],
        ite(
            data.len() == 0,
            ListObject.empty(IntObject),
            ite(
                call("Select-pred", BoolObject, data[0]),
                call("Select", ListObject[IntObject], data[1:]).append(data[0]),
                call("Select", ListObject[IntObject], data[1:]),
            ),
        ),
        data,
    )
    select_func1 = fn_decl_recursive(
        "Select1",
        ListObject[IntObject],
        ite(
            data.len() == 0,
            ListObject.empty(IntObject),
            ite(
                call("Select-pred1", BoolObject, data[0]),
                call("Select1", ListObject[IntObject], data[1:]).append(data[0]),
                call("Select1", ListObject[IntObject], data[1:]),
            ),
        ),
        data,
    )
    select_func2 = fn_decl_recursive(
        "Select2",
        ListObject[IntObject],
        ite(
            data.len() == 0,
            ListObject.empty(IntObject),
            ite(
                call("Select-pred2", BoolObject, data[0]),
                call("Select2", ListObject[IntObject], data[1:]).append(data[0]),
                call("Select2", ListObject[IntObject], data[1:]),
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

def ps_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> BoolObject:
    # reads = [in_lst]
    ret_val = writes[0]
    in_lst = reads[0]
    return choose(
        ret_val == in_lst,
        ret_val == call("Select", ListObject[IntObject], in_lst),
        ret_val == call("Select1", ListObject[IntObject], in_lst),
        ret_val == call("Select2", ListObject[IntObject], in_lst)
    )

def inv_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> BoolObject:
    # writes = [out, i]
    # reads = [in]
    out_lst, i = writes[0], writes[1]
    in_lst = reads[0]
    lst = choose(in_lst, out_lst, call("Select", ListObject[IntObject], in_lst))
    lst_inv_cond = choose(
        lst + call("Select", ListObject[IntObject], lst[i:]) == lst,
        out_lst + lst[i:] == lst
    )

    in_lst_length = in_lst.len()
    i_bound_in_lst_length_cond = choose(
        i >= in_lst_length,
        i <= in_lst_length,
        i > in_lst_length,
        i < in_lst_length,
        i == in_lst_length,
    )
    i_bound_int_lit = choose(IntObject(0), IntObject(1))
    i_bound_int_lit_cond = choose(
        i >= i_bound_int_lit,
        i <= i_bound_int_lit,
        i > i_bound_int_lit,
        i < i_bound_int_lit,
        i == i_bound_int_lit,
    )
    return choose(and_objects(i_bound_int_lit_cond, i_bound_in_lst_length_cond, lst_inv_cond))

if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        "tests/llvm/vector1.ll",
        "tests/llvm/vector1.loops",
        "test",
        target_lang,
        defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar
    )

    in_var = ListObject(IntObject, "in")
    driver.add_var_object(in_var)
    test(in_var)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))