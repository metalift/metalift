# from typing import List, Union, get_args

# from mypy.nodes import Statement

# from metalift.frontend.llvm import Driver
# from metalift.ir import (And, Bool, BoolLit, Call, Choose, Eq, Expr, FnDecl,FnDeclRecursive, Ge, Gt, Int, IntLit, Ite, Le, ListT, Lt, Var, 
#     ListObject, IntObject, NewObject, BoolObject)
# from tests.python.utils.utils import codegen


# def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
#     arg = Var("n", Int())
#     select_pred = FnDecl("Select-pred", Bool(), Gt(arg, IntLit(2)), arg)
#     select_pred1 = FnDecl("Select-pred1", Bool(), Lt(arg, IntLit(10)), arg)
#     select_pred2 = FnDecl("Select-pred2", Bool(), And(Gt(arg, IntLit(2)), Lt(arg, IntLit(10))), arg)

#     # data = Var("l", ListT(Int()))
#     data = ListObject(IntObject, "l")
#     select_func = FnDeclRecursive(
#         "Select",
#         # ListT(Int()),
#         ListObject(IntObject),
#         Ite(
#             # Eq(Call("list_length", Int(), data), IntLit(0)),
#             data.len() == 0,
#             # Call("list_empty", ListT(Int())),
#             ListObject.empty(IntObject),
#             Ite(
#                 # Call("Select-pred", Bool(), Call("list_get", Int(), data, IntLit(0))),
#                 Call("Select-pred", Bool(), data[0]),
#                 Call(
#                     "list_append",
#                     ListT(Int()),
#                     Call(
#                         "Select",
#                         ListT(Int()),
#                         Call("list_tail", ListT(Int()), data, IntLit(1)),
#                     ),
#                     # Call("list_get", Int(), data, IntLit(0)),
#                     data[0]
#                 ),
#                 # Call(
#                 #     "Select",
#                 #     ListT(Int()),
#                 #     Call("list_tail", ListT(Int()), data.src, IntLit(1)),
#                 # ),
#                 Call(
#                     "Select",
#                     ListT(Int()),
#                     Call("list_tail", ListT(Int()), data, IntLit(1)),
#                 ),
#             ),
#         ),
#         data,
#     )
#     select_func1 = FnDeclRecursive(
#         "Select1",
#         ListT(Int()),
#         Ite(
#             data.len() == 0,
#             ListObject.empty(Int),
#             Ite(
#                 Call("Select-pred1", Bool(), data[0]),
#                 Call(
#                     "list_append",
#                     ListT(Int()),
#                     Call(
#                         "Select1",
#                         ListT(Int()),
#                         Call("list_tail", ListT(Int()), data, IntLit(1)),
#                     ),
#                     data[0]
#                 ),
#                 Call(
#                     "Select1",
#                     ListT(Int()),
#                     Call("list_tail", ListT(Int()), data, IntLit(1)),
#                 ),
#             ),
#         ),
#         data,
#     )
#     select_func2 = FnDeclRecursive(
#         "Select2",
#         ListT(Int()),
#         Ite(
#             data.len() == 0,
#             ListObject.empty(Int),
#             Ite(
#                 Call("Select-pred2", Bool(), data[0]),
#                 Call(
#                     "list_append",
#                     ListT(Int()),
#                     Call(
#                         "Select2",
#                         ListT(Int()),
#                         Call("list_tail", ListT(Int()), data, IntLit(1)),
#                     ),
#                     data[0],
#                 ),
#                 Call(
#                     "Select2",
#                     ListT(Int()),
#                     Call("list_tail", ListT(Int()), data, IntLit(1)),
#                 ),
#             ),
#         ),
#         data,
#     )

#     return [
#         select_pred,
#         select_pred1,
#         select_pred2,
#         select_func,
#         select_func1,
#         select_func2,
#     ]

# def ps_grammar(ret_val: NewObject, writes: List[NewObject], reads: List[NewObject]) -> Expr:
#     # reads = [in_lst]
#     return Choose(
#         Call("list_eq", Bool(), ret_val, *reads),
#         Call("list_eq", Bool(), ret_val, Call("Select", ListT(Int()), *reads)),
#         Call("list_eq", Bool(), ret_val, Call("Select1", ListT(Int()), *reads)),
#         Call("list_eq", Bool(), ret_val, Call("Select2", ListT(Int()), *reads))
#     )

# def inv_grammar(v: NewObject, writes: List[NewObject], reads: List[NewObject]) -> Expr:
#     # This grammar func could be called with v as `i` or `out_lst`, and we really only want to generate this grammar once.
#     if v.var_name() != "out":
#         return BoolLit(True)

#     # writes = [out, i]
#     # reads = [in]
#     out_lst, i = writes[0], writes[1]
#     in_lst = reads[0]


#     print("in_lst:", in_lst.type)

#     # lst = Choose(in_lst, out_lst, Call("Select", ListT(Int()), in_lst))
#     lst = Choose(in_lst, out_lst, Call("Select", ListObject(IntObject), in_lst))
#     lst_inv_cond = Choose(
#         Call(
#             "list_eq",
#             Bool(),
#             Call(
#                 "list_append",
#                 ListT(Int()),
#                 lst,
#                 Call(
#                     "Select",
#                     ListT(Int()),
#                     Call("list_tail", ListT(Int()), lst, i),
#                 ),
#             ),
#             lst,
#         ),
#         Call(
#             "list_eq",
#             Bool(),
#             Call(
#                 "list_concat",
#                 ListT(Int()),
#                 out_lst,
#                 Call("list_tail", ListT(Int()), lst, i),
#             ),
#             lst,
#         ),
#     )

#     # in_lst_length = Call("list_length", Int(), in_lst)
#     in_lst_length = in_lst.len()
#     i_bound_in_lst_length_cond = Choose(
#         Ge(i, in_lst_length),
#         Le(i, in_lst_length),
#         Gt(i, in_lst_length),
#         Lt(i, in_lst_length),
#         Eq(i, in_lst_length),
#     )
#     i_bound_int_lit = Choose(IntLit(0), IntLit(1))
#     i_bound_int_lit_cond = Choose(
#         Ge(i, i_bound_int_lit),
#         Le(i, i_bound_int_lit),
#         Gt(i, i_bound_int_lit),
#         Lt(i, i_bound_int_lit),
#         Eq(i, i_bound_int_lit),
#     )
#     return Choose(And(And(i_bound_int_lit_cond, i_bound_in_lst_length_cond), lst_inv_cond))

from typing import List, Union
from collections import defaultdict

from mypy.nodes import Statement

from metalift.frontend.llvm import Driver
from metalift.ir import And, Bool, BoolLit, Call, Choose, Eq, Expr, FnDecl,FnDeclRecursive, Ge, Gt, Int, IntLit, Ite, Le, ListT, Lt, Var, NewObject, ListObject, IntObject
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

def ps_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Expr:
    # reads = [in_lst]
    ret_val = writes[0]
    in_lst = reads[0]
    return choose(
        ret_val == in_lst,
        ret_val == call("Select", mlList[Int], in_lst),
        ret_val == call("Select1", mlList[Int], in_lst),
        ret_val == call("Select2", mlList[Int], in_lst)
    )

def inv_grammar(v: Var, writes: List[Var], reads: List[Var]) -> Expr:
    # This grammar func could be called with v as `i` or `out_lst`, and we really only want to generate this grammar once.
    if v.var_name() != "out":
        return BoolLit(True)

    # writes = [out, i]
    # reads = [in]
    out_lst, i = writes[1], writes[0]
    in_lst = reads[0]
    lst = Choose(in_lst, out_lst, Call("Select", ListObject(IntObject), in_lst))
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
                out_lst,
                Call("list_tail", ListT(Int()), lst, i),
            ),
            lst,
        ),
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
    return choose(and_objects(i_bound_int_lit_cond, i_bound_in_lst_length_cond, lst_inv_cond))

if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        llvm_filepath="tests/llvm/list1.ll",
        loops_filepath="tests/llvm/list1.loops",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammars=defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar=ps_grammar
    )

    v1 = ListObject(IntObject, "in")
    driver.add_var_object(v1)

    test(v1)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))
