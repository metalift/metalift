from typing import Callable, Dict, List, Literal, NamedTuple, Optional, Tuple

from llvmlite.binding import ValueRef

from metalift.ir import Call, Expr, NewObject, ListObject, IntObject, TupleObject
from metalift.vc_util import parseOperand

ReturnValue = NamedTuple(
    "ReturnValue",
    [
        ("val", Optional[NewObject]),
        ("assigns", Optional[List[Tuple[str, NewObject, str]]]),
    ],
)


def new_list(
    primitive_vars: Dict[str, NewObject],
    pointer_vars: Dict[str, NewObject],
    global_vars: Dict[str, str],
    *args: ValueRef,
) -> ReturnValue:
    return ReturnValue(ListObject.empty(IntObject), None)


def list_length(
    primitive_vars: Dict[str, NewObject],
    pointer_vars: Dict[str, NewObject],
    global_vars: Dict[str, str],
    *args: ValueRef,
) -> ReturnValue:
    assert len(args) == 1
    # TODO(jie) think of how to better handle list of lists
    lst = (
        primitive_vars[args[0].name]
        if not args[0].type.is_pointer
        else pointer_vars[args[0].name]
    )
    return ReturnValue(
        lst.len(),
        None,
    )


def list_get(
    primitive_vars: Dict[str, NewObject],
    pointer_vars: Dict[str, NewObject],
    global_vars: Dict[str, str],
    *args: ValueRef,
) -> ReturnValue:
    assert len(args) == 2
    lst = (
        primitive_vars[args[0].name]
        if not args[0].type.is_pointer
        else pointer_vars[args[0].name]
    )
    index = primitive_vars[args[1].name]
    return ReturnValue(
        lst[index],
        None,
    )


def list_append(
    primitive_vars: Dict[str, NewObject],
    pointer_vars: Dict[str, NewObject],
    global_vars: Dict[str, str],
    *args: ValueRef,
) -> ReturnValue:
    assert len(args) == 2
    lst = (
        primitive_vars[args[0].name]
        if not args[0].type.is_pointer
        else pointer_vars[args[0].name]
    )
    value = (
        primitive_vars[args[1].name]
        if not args[1].type.is_pointer
        else pointer_vars[args[1].name]
    )
    return ReturnValue(
        lst.append(value),
        None,
    )


def list_concat(
    primitive_vars: Dict[str, NewObject],
    pointer_vars: Dict[str, NewObject],
    global_vars: Dict[str, str],
    *args: ValueRef,
) -> ReturnValue:
    assert len(args) == 2
    lst1 = (
        primitive_vars[args[0].name]
        if not args[0].type.is_pointer
        else pointer_vars[args[0].name]
    )
    lst2 = (
        primitive_vars[args[1].name]
        if not args[1].type.is_pointer
        else pointer_vars[args[1].name]
    )
    return ReturnValue(
        lst1 + lst2,
        None,
    )


def new_vector(
    primitive_vars: Dict[str, Expr],
    pointer_vars: Dict[str, Expr],
    global_vars: Dict[str, str],
    *args: ValueRef,
) -> ReturnValue:
    assert len(args) == 1
    var_name: str = args[0].name
    assigns: List[Tuple[str, Expr]] = [
        (var_name, Call("list_empty", Type("MLList", Int())), "primitive")
    ]
    return ReturnValue(None, assigns)


def vector_append(
    primitive_vars: Dict[str, Expr],
    pointer_vars: Dict[str, Expr],
    global_vars: Dict[str, str],
    *args: ValueRef,
) -> ReturnValue:
    assert len(args) == 2
    assign_var_name: str = args[0].name

    # TODO: fix where the args is in pointer or primitive
    assign_val = Call(
        "list_append",
        parse_type_ref(args[0].type),
        primitive_vars[args[0].name]
        if not args[0].type.is_pointer
        else pointer_vars[args[0].name],
        primitive_vars[args[1].name]
        if not args[1].type.is_pointer
        else pointer_vars[args[1].name],
    )
    return ReturnValue(
        None,
        [(assign_var_name, assign_val, "primitive")],
    )


def new_tuple(
    primitive_vars: Dict[str, Expr],
    pointer_vars: Dict[str, Expr],
    global_vars: Dict[str, str],
    *args: ValueRef,
) -> ReturnValue:
    return ReturnValue(Call("newTuple", Type("Tuple", Int(), Int())), None)


def make_tuple(
    primitive_vars: Dict[str, Expr],
    pointer_vars: Dict[str, Expr],
    global_vars: Dict[str, str],
    *args: ValueRef,
) -> ReturnValue:
    reg_vals = [
        primitive_vars[args[i].name]
        if not args[i].type.is_pointer
        else pointer_vars[args[i].name]
        for i in range(len(args))
    ]

    # TODO(jie): handle types other than IntObject
    tuple_length = len(args)
    if tuple_length == 1:
        literal_type = Literal[1]
    elif tuple_length == 2:
        literal_type = Literal[2]
    elif tuple_length == 3:
        literal_type = Literal[3]

    else:
        raise Exception("Make tuple only supports length <= 3")

    return_type = TupleObject[IntObject, literal_type]

    call_expr = Call("make-tuple", return_type, *reg_vals)
    return ReturnValue(return_type(IntObject, literal_type, call_expr), None)

def tuple_get(
    primitive_vars: Dict[str, Expr],
    pointer_vars: Dict[str, Expr],
    global_vars: Dict[str, str],
    *args: ValueRef,
) -> ReturnValue:
    return ReturnValue(
        Call(
            "tupleGet",
            IntObject,
            primitive_vars[args[0].name]
            if not args[0].type.is_pointer
            else pointer_vars[args[0].name],
            parseOperand(args[1], primitive_vars),
        ),
        None,
    )


def get_field(
    primitive_vars: Dict[str, Expr],
    pointer_vars: Dict[str, Expr],
    global_vars: Dict[str, str],
    *args: ValueRef,
) -> ReturnValue:
    (fieldName, obj) = args
    val = pointer_vars[obj.name].args[fieldName.args[0]]
    # primitive_vars[i] = pointer_vars[obj].args[fieldName.args[0]
    return ReturnValue(val, None)


def set_field(
    primitive_vars: Dict[str, Expr],
    pointer_vars: Dict[str, Expr],
    global_vars: Dict[str, str],
    *args: ValueRef,
) -> ReturnValue:
    (fieldName, obj, val) = args
    pointer_vars[obj.name].args[fieldName.args[0]] = primitive_vars[val.name]
    # XXX: not tracking pointer_varsory writes as assigns for now. This might be fine for now since all return vals must be loaded to primitive_vars
    return ReturnValue(None, None)


fn_models: Dict[str, Callable[..., ReturnValue]] = {
    # list methods
    "newList": new_list,
    "listLength": list_length,
    "listAppend": list_append,
    "listGet": list_get,
    # vector methods
    "vector": new_vector,
    "size": list_length,
    "push_back": vector_append,
    "operator[]": list_get,
    "getField": get_field,
    "setField": set_field,
    # names for set.h
    "set_create": lambda primitive_vars, pointer_vars, global_vars, *args: ReturnValue(
        Call("set-create", SetT(Int())), None
    ),
    "set_add": lambda primitive_vars, pointer_vars, global_vars, *args: ReturnValue(
        Call(
            "set-insert",
            SetT(Int()),
            parseOperand(args[1], primitive_vars),
            parseOperand(args[0], pointer_vars),
        ),
        None,
    ),
    "set_remove": lambda primitive_vars, pointer_vars, global_vars, *args: ReturnValue(
        Call(
            "set-minus",
            SetT(Int()),
            parseOperand(args[0], pointer_vars),
            Call("set-singleton", SetT(Int()), parseOperand(args[1], primitive_vars)),
        ),
        None,
    ),
    "set_contains": lambda primitive_vars, pointer_vars, global_vars, *args: ReturnValue(
        Ite(
            Call(
                "set-pointer_varsber",
                Bool(),
                parseOperand(args[1], primitive_vars),
                parseOperand(args[0], pointer_vars),
            ),
            IntLit(1),
            IntLit(0),
        ),
        None,
    ),
    # tuple methods
    "MakeTuple": make_tuple,
    "tupleGet": tuple_get,
}
