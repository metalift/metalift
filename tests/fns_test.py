from metalift import ir
from metalift.ir import (
    Eq,
    Call,
    Int,
    IntLit,
    FnDecl,
    Var,
    Ite,
    List,
    Bool,
    Fn,
    PrintMode,
)

f = Var("f", Fn(Bool()))
data = Var("l", List(Int()))


def list_length(l):
    return Call("list_length", Int(), l)


def list_empty():
    return Call("list_empty", List(Int()))


def list_get(l, i):
    return Call("list_get", Int(), l, i)


def list_tail(l, i):
    return Call("list_tail", List(Int()), l, i)


def list_append(l1, l2):
    return Call("list_append", List(Int()), l1, l2)


ir.printMode = PrintMode.RosetteVC
select_func = FnDecl(
    "Select",
    List(Int()),
    Ite(
        Eq(list_length(data), IntLit(0)),
        list_empty(),
        Ite(
            Call(f.args[0], Bool(), list_get(data, IntLit(0))),
            list_append(
                Call("Select", List(Int()), list_tail(data, IntLit(1)), f),
                list_get(data, IntLit(0)),
            ),
            Call("Select", List(Int()), list_tail(data, IntLit(1)), f),
        ),
    ),
    data,
    f,
)
print(select_func)
