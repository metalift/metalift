from collections import defaultdict
from typing import List, Union

from metalift.frontend.llvm import Driver
from metalift.ir import And, BoolObject, Call, Choose, Eq, Expr, FnDecl,FnDeclRecursive, Ge, Gt, IntObject, ListObject, Ite, Le, Lt, NewObject, Var, call, choose, ite
from metalift.vc_util import and_objects
from tests.python.utils.utils import codegen


def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    arg = IntObject("n")
    select_pred = FnDecl("Select-pred", BoolObject, (arg > 2).src, arg.src)
    select_pred1 = FnDecl("Select-pred1", BoolObject, (arg < 10).src, arg.src)
    select_pred2 = FnDecl("Select-pred2", BoolObject, (arg > 2).And(arg < 10), arg.src)

    data = ListObject(IntObject, "l")
    select_func = FnDeclRecursive(
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
        ).src,
        data.src,
    )
    select_func1 = FnDeclRecursive(
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
        ).src,
        data.src,
    )
    select_func2 = FnDeclRecursive(
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
        ).src,
        data.src,
    )

    return [
        select_pred,
        select_pred1,
        select_pred2,
        select_func,
        select_func1,
        select_func2,
    ]

def ps_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> Expr:
    # reads = [in_lst]
    import pdb; pdb.set_trace()
    ret_val = writes[0]
    in_lst = reads[0]
    return choose(
        ret_val == in_lst,
        ret_val == call("Select", ListObject[IntObject], in_lst),
        ret_val == call("Select1", ListObject[IntObject], in_lst),
        ret_val == call("Select2", ListObject[IntObject], in_lst)
    )

def inv_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> Expr:
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
        defaultdict(lambda: inv_grammar),
        ps_grammar
    )

    in_var = ListObject(IntObject, "in")
    driver.add_var_object(in_var)
    test(in_var)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))