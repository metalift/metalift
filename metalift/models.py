from typing import Callable, Dict, List, NamedTuple, Optional, Tuple

from llvmlite.binding import ValueRef

from metalift.ir import Expr, Int
from metalift.ir import List as mlList
from metalift.ir import Object
from metalift.ir import Set as mlSet
from metalift.ir import call, make_tuple_type, parse_type_ref_to_obj
from metalift.vc_util import parse_operand

ReturnValue = NamedTuple(
    "ReturnValue",
    [
        ("val", Optional[Object]),
        ("assigns", Optional[List[Tuple[str, Object, str]]]),
    ],
)


def set_create(
    primitive_vars: Dict[str, Object],
    pointer_vars: Dict[str, Object],
    global_vars: Dict[str, str],
    *args: ValueRef,
) -> ReturnValue:
    return ReturnValue(mlSet.empty(Int), None)


def set_add(
    primitive_vars: Dict[str, Object],
    pointer_vars: Dict[str, Object],
    global_vars: Dict[str, str],
    *args: ValueRef,
) -> ReturnValue:
    assert len(args) == 2
    s = (
        primitive_vars[args[0].name]
        if not args[0].type.is_pointer
        else pointer_vars[args[0].name]
    )
    item = primitive_vars[args[1].name]
    return ReturnValue(s.add(item), None)  # type: ignore


def set_remove(
    primitive_vars: Dict[str, Object],
    pointer_vars: Dict[str, Object],
    global_vars: Dict[str, str],
    *args: ValueRef,
) -> ReturnValue:
    assert len(args) == 2
    s = (
        primitive_vars[args[0].name]
        if not args[0].type.is_pointer
        else pointer_vars[args[0].name]
    )
    item = primitive_vars[args[1].name]
    return ReturnValue(s.remove(item), None)  # type: ignore


def set_contains(
    primitive_vars: Dict[str, Object],
    pointer_vars: Dict[str, Object],
    global_vars: Dict[str, str],
    *args: ValueRef,
) -> ReturnValue:
    assert len(args) == 2
    s = (
        primitive_vars[args[0].name]
        if not args[0].type.is_pointer
        else pointer_vars[args[0].name]
    )
    item = primitive_vars[args[1].name]
    return ReturnValue(item in s, None)  # type: ignore


def new_list(
    primitive_vars: Dict[str, Object],
    pointer_vars: Dict[str, Object],
    global_vars: Dict[str, str],
    *args: ValueRef,
) -> ReturnValue:
    assert len(args) == 0
    return ReturnValue(mlList.empty(Int), None)


def list_length(
    primitive_vars: Dict[str, Object],
    pointer_vars: Dict[str, Object],
    global_vars: Dict[str, str],
    *args: ValueRef,
) -> ReturnValue:
    assert len(args) == 1
    # TODO think of how to better handle list of lists
    lst = (
        primitive_vars[args[0].name]
        if not args[0].type.is_pointer
        else pointer_vars[args[0].name]
    )
    return ReturnValue(
        lst.len(),  # type: ignore
        None,
    )


def list_get(
    primitive_vars: Dict[str, Object],
    pointer_vars: Dict[str, Object],
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
        lst[index],  # type: ignore
        None,
    )


def list_append(
    primitive_vars: Dict[str, Object],
    pointer_vars: Dict[str, Object],
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
        lst.append(value),  # type: ignore
        None,
    )


def list_concat(
    primitive_vars: Dict[str, Object],
    pointer_vars: Dict[str, Object],
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
        lst1 + lst2,  # type: ignore
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
    assigns: List[Tuple[str, Expr, str]] = [
        (var_name, mlList.empty(Int), "primitive")  # type: ignore
    ]
    return ReturnValue(None, assigns)  # type: ignore


def vector_append(
    primitive_vars: Dict[str, Expr],
    pointer_vars: Dict[str, Expr],
    global_vars: Dict[str, str],
    *args: ValueRef,
) -> ReturnValue:
    assert len(args) == 2
    assign_var_name: str = args[0].name

    assign_val = call(
        "list_append",
        parse_type_ref_to_obj(args[0].type),
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
    return ReturnValue(call("newTuple", make_tuple_type(Int, Int)), None)


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

    # TODO: handle types other than Int
    contained_type = [Int for i in range(len(args))]
    return_type = make_tuple_type(*contained_type)
    return ReturnValue(call("make-tuple", return_type, *reg_vals), None)


def tuple_get(
    primitive_vars: Dict[str, Expr],
    pointer_vars: Dict[str, Expr],
    global_vars: Dict[str, str],
    *args: ValueRef,
) -> ReturnValue:
    return ReturnValue(
        call(
            "tupleGet",
            Int,
            primitive_vars[args[0].name]
            if not args[0].type.is_pointer
            else pointer_vars[args[0].name],
            parse_operand(args[1], primitive_vars),
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
    "set_create": set_create,
    "set_add": set_add,
    "set_remove": set_remove,
    "set_contains": set_contains,
    # tuple methods
    "MakeTuple": make_tuple,
    "tupleGet": tuple_get,
}
