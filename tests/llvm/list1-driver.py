from typing import List

from metalift.frontend.llvm import Driver
from metalift.ir import (Add, And, Call, Choose, Eq, Expr, Bool, Ge, Ite, FnT, CallValue,
                         Le, Gt, Lt, Int, IntLit, ListT, FnDeclRecursive, Var)
from tests.python.utils.utils import codegen

def target_lang():

    arg = Var("n", Int())
    select_pred = FnDeclRecursive("Select-pred", FnT(Bool()), Gt(arg, IntLit(2)), arg)
    select_pred1 = FnDeclRecursive("Select-pred1", FnT(Bool()), Lt(arg, IntLit(10)), arg)
    select_pred2 = FnDeclRecursive("Select-pred2", FnT(Bool()), And(Gt(arg, IntLit(2)), Lt(arg, IntLit(10))), arg)
    data = Var("l", ListT(Int()))
    f = Var("f", FnT(Bool()))
    select_func = FnDeclRecursive(
        "Select",
        ListT(Int()),
        Ite(
            Eq(Call("list_length", Int(), data), IntLit(0)),
            Call("list_empty", ListT(Int())),
            Ite(
                CallValue(f, Call("list_get", Int(), data, IntLit(0))),
                Call(
                    "list_append",
                    ListT(Int()),
                    Call(
                        "Select",
                        ListT(Int()),
                        Call("list_tail", ListT(Int()), data, IntLit(1)),
                        f,
                    ),
                    Call("list_get", Int(), data, IntLit(0)),
                ),
                Call(
                    "Select",
                    ListT(Int()),
                    Call("list_tail", ListT(Int()), data, IntLit(1)),
                    f,
                ),
            ),
        ),
        data,
        f,
    )

    return [select_pred, select_pred1, select_pred2, select_func]

    arg = Var("n", Int())
    select_pred = FnDeclRecursive("Select-pred", Bool(), Gt(arg, IntLit(2)), arg)
    select_pred1 = FnDeclRecursive("Select-pred1", Bool(), Lt(arg, IntLit(10)), arg)
    select_pred2 = FnDeclRecursive("Select-pred2", Bool(), And(Gt(arg, IntLit(2)), Lt(arg, IntLit(10))), arg)
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

def inv_grammar(v: Var, writes: List[Var], reads: List[Var]) -> Expr:
    f = Choose(
        Call("Select-pred", FnT(Bool(), *reads)),
        Call("Select-pred1", FnT(Bool(), *reads)),
        Call("Select-pred2", FnT(Bool(), *reads)),
    )
    a = Choose(
        writes[0],
        *reads,
        Call("Select", ListT(Int()), *reads, f)
    )
    i = Choose(IntLit(0), IntLit(1))
    e = Choose(
        Call(
            "list_eq",
            Bool(),
            Call(
                "list_concat",
                ListT(Int()),
                a,
                Call(
                    "Select",
                    ListT(Int()),
                    Call("list_tail", ListT(Int()), a, writes[1]),
                    f,
                ),
            ),
            a,
        ),
        Call(
            "list_eq",
            Bool(),
            Call(
                "list_concat",
                ListT(Int()),
                a,
                Call("list_tail", ListT(Int()), a, writes[1]),
            ),
            a,
        ),
    )
    d = Choose(
        Ge(writes[1], Call("list_length", Int(), *reads)),
        Le(writes[1], Call("list_length", Int(), *reads)),
        Gt(writes[1], Call("list_length", Int(), *reads)),
        Lt(writes[1], Call("list_length", Int(), *reads)),
        Eq(writes[1], Call("list_length", Int(), *reads)),
    )
    c = Choose(
        Ge(writes[1], i),
        Le(writes[1], i),
        Gt(writes[1], i),
        Lt(writes[1], i),
        Eq(writes[1], i),
    )
    b = Choose(And(And(c, d), e))
    return b


    a = Choose(
        writes[0], *reads, Call("Select", ListT(Int()), *reads)
    )
    i = Choose(IntLit(0), IntLit(1))
    e = Choose(
        Call(
            "list_eq",
            Bool(),
            Call(
                "list_append",
                ListT(Int()),
                a,
                Call(
                    "Select",
                    ListT(Int()),
                    Call("list_tail", ListT(Int()), a, writes[1]),
                ),
            ),
            a,
        ),
        Call(
            "list_eq",
            Bool(),
            Call(
                "list_concat",
                ListT(Int()),
                a,
                Call("list_tail", ListT(Int()), a, writes[1]),
            ),
            a,
        ),
    )
    d = Choose(
        Ge(writes[1], Call("list_length", Int(), *reads)),
        Le(writes[1], Call("list_length", Int(), *reads)),
        Gt(writes[1], Call("list_length", Int(), *reads)),
        Lt(writes[1], Call("list_length", Int(), *reads)),
        Eq(writes[1], Call("list_length", Int(), *reads)),
    )
    c = Choose(
        Ge(writes[1], i),
        Le(writes[1], i),
        Gt(writes[1], i),
        Lt(writes[1], i),
        Eq(writes[1], i),
    )
    b = Choose(And(And(c, d), e))
    return b

def ps_grammar(ret_val: Var, writes: List[Var], reads: List[Var]) -> Expr:
    rv = writes[0]
    fns = Choose(
        Call("Select-pred", FnT(Bool(), rv)),
        Call("Select-pred1", FnT(Bool(), rv)),
        Call("Select-pred2", FnT(Bool(), rv)),
    )
    choices = Choose(
        Call("list_eq", Bool(), rv, *reads),
        (
            Call(
                "list_eq",
                Bool(),
                rv,
                Call("Select", ListT(Int()), *reads, fns),
            )
        ),
    )
    return choices


    rv = writes[0]
    choices = Choose(
        Call("list_eq", Bool(), rv, *reads),
        (Call("list_eq", Bool(), rv, Call("Select", ListT(Int()), *reads))),
        (Call("list_eq", Bool(), rv, Call("Select1", ListT(Int()), *reads))),
        (Call("list_eq", Bool(), rv, Call("Select2", ListT(Int()), *reads))),
    )
    return choices

if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        llvm_filepath="tests/llvm/list1.ll",
        loops_filepath="tests/llvm/list1.loops",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammar=inv_grammar,
        ps_grammar=ps_grammar
    )

    input = driver.variable("in", ListT(Int()))

    test(input)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))