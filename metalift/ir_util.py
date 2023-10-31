import typing
from typing import Union, Type as typingType, _GenericAlias, get_args, get_origin
from metalift.ir import Expr, ListObject, NewObject, SetObject, TupleObject, Type as irType

# TODO(jie): get rid of this once old types are all removed
MLType = Union[irType, typingType]

def is_list_type_expr(expr: Expr) -> bool:
    if isinstance(expr.type, _GenericAlias):
        return issubclass(get_origin(expr.type), ListObject)
    else:
        return issubclass(expr.type, ListObject)

def is_nested_list_type_expr(expr: Expr) -> bool:
    contained_type = get_args(expr.type)[0]
    return is_list_type_expr(expr) and isinstance(contained_type, _GenericAlias) and issubclass(get_origin(contained_type), ListObject)

def get_nested_list_element_type(expr: Expr) -> typing.Type[NewObject]:
    if not is_nested_list_type_expr(expr):
        raise Exception("expr is not a nested list!")
    contained_type = get_args(expr.type)[0]
    return get_args(contained_type)[0]

def is_set_type_expr(expr: Expr) -> bool:
    if isinstance(expr.type, _GenericAlias):
        return issubclass(get_origin(expr.type), SetObject)
    else:
        return issubclass(expr.type, SetObject)

def is_tuple_type_expr(expr: Expr) -> bool:
    if isinstance(expr.type, _GenericAlias):
        return issubclass(get_origin(expr.type), TupleObject)
    else:
        return issubclass(expr.type, TupleObject)


# Helper functions
def is_object_pointer_type(obj: NewObject) -> bool:
    return isinstance(obj, ListObject) or isinstance(obj, SetObject)