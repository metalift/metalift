from typing import Callable, Dict, List, Literal, NamedTuple, Optional, Tuple, cast

from llvmlite.binding import ValueRef

from metalift.ir import Expr, NewObject, ListObject, IntObject
from metalift.vc_util import parseOperand

# ReturnValue = NamedTuple(
#     "ReturnValue",
#     [
#         ("val", Optional[Expr]),
#         ("assigns", Optional[List[Tuple[str, Expr]]]),
#     ],
# )
ReturnValue = NamedTuple(
    "ReturnValue",
    [
        ("val", Optional[NewObject]),
        ("assigns",  Optional[List[Tuple[str, NewObject]]]),
    ],
)

def new_list(
    primitive_vars: Dict[str, NewObject],
    pointer_vars: Dict[str, NewObject],
    global_vars: Dict[str, str],
    *args: ValueRef,
) -> ReturnValue:
    # return ReturnValue(Call("list_empty", Type("MLList", Int())), None)
     return ReturnValue(ListObject.empty(IntObject), None)


def list_length(
    primitive_vars: Dict[str, NewObject],
    pointer_vars: Dict[str, NewObject],
    global_vars: Dict[str, str],
    *args: ValueRef,
) -> ReturnValue:
    # return ReturnValue(Call("list_length", Int(), primitive_vars[args[0].name]), None)
    return ReturnValue(
        primitive_vars[args[0].name].len(), 
        None,
    )

def list_get(
    primitive_vars: Dict[str, NewObject],
    pointer_vars: Dict[str, NewObject],
    global_vars: Dict[str, str],
    *args: ValueRef,
) -> ReturnValue:
    # return ReturnValue(
    #     Call(
    #         "list_get",
    #         Int(),
    #         primitive_vars[args[0].name],
    #         primitive_vars[args[1].name],
    #     ),
    #     None,
    # )
    return ReturnValue(
        primitive_vars[args[0].name][primitive_vars[args[1].name]],
        None,
    )


def list_append(
    primitive_vars: Dict[str, NewObject],
    pointer_vars: Dict[str, NewObject],
    global_vars: Dict[str, str],
    *args: ValueRef,
) -> ReturnValue:
    # return ReturnValue(
    #     Call(
    #         "list_append",
    #         parse_type_ref(args[0].type),
    #         primitive_vars[args[0].name],
    #         primitive_vars[args[1].name],
    #     ),
    #     None,
    # )
    # print(primitive_vars[args[0].name])
    print(args[1].name)
    print(primitive_vars[args[1].name])
    # print(IntObject(primitive_vars[args[1].name]).type)
    return ReturnValue(
        primitive_vars[args[0].name].append(IntObject(primitive_vars[args[1].name])),
        None,
    )


def list_concat(
    primitive_vars: Dict[str, NewObject],
    pointer_vars: Dict[str, NewObject],
    global_vars: Dict[str, str],
    *args: ValueRef,
) -> ReturnValue:
    # return ReturnValue(
    #     Call(
    #         "list_concat",
    #         parse_type_ref(args[0].type),
    #         primitive_vars[args[0].name],
    #         primitive_vars[args[1].name],
    #     ),
    #     None,
    # )
    return ReturnValue(
        primitive_vars[args[0].name] + primitive_vars[args[1].name], 
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

    # TODO: fix where the args is in pointer or primitive
    assign_val = Call(
        "list_append",
        parse_type_ref(args[0].type),
        primitive_vars[args[0].name] if args[0].name in primitive_vars else pointer_vars[args[0].name],
        primitive_vars[args[1].name] if args[1].name in primitive_vars else pointer_vars[args[1].name],
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

    # TODO(jie): handle types other than Int
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
    "set_create": set_create,
    "set_add": set_add,
    "set_remove": set_remove,
    "set_contains": set_contains,
    # tuple methods
    "MakeTuple": make_tuple,
    "tupleGet": tuple_get,
}
