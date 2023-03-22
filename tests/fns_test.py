from metalift import ir
from metalift.ir import (
    Eq,
    Call,
    Int,
    IntLit,
    FnDeclRecursive,
    Var,
    Ite,
    ListT,
    Bool,
    FnT,
    PrintMode,
)

f = Var("f", FnT(Bool()))
data = Var("l", ListT(Int()))


def list_length(l):
    return Call("list_length", Int(), l)


def list_empty():
    return Call("list_empty", ListT(Int()))


def list_get(l, i):
    return Call("list_get", Int(), l, i)


def list_tail(l, i):
    return Call("list_tail", ListT(Int()), l, i)


def list_append(l1, l2):
    return Call("list_append", ListT(Int()), l1, l2)


ir.printMode = PrintMode.RosetteVC
select_func = FnDeclRecursive(
    "Select",
    ListT(Int()),
    Ite(
        Eq(list_length(data), IntLit(0)),
        list_empty(),
        Ite(
            Call(f.args[0], Bool(), list_get(data, IntLit(0))),
            list_append(
                Call("Select", ListT(Int()), list_tail(data, IntLit(1)), f),
                list_get(data, IntLit(0)),
            ),
            Call("Select", ListT(Int()), list_tail(data, IntLit(1)), f),
        ),
    ),
    data,
    f,
)
print(select_func)
