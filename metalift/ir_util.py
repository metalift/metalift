from typing import Union, Type as typingType, _GenericAlias, get_origin
from metalift.ir import (
    Expr,
    ListObject,
    NewObject,
    SetObject,
    TupleObject,
    Type as irType,
)

# TODO(jie): get rid of this once old types are all removed
MLType = Union[irType, typingType]


def is_list_type_expr(expr: Expr) -> bool:
    if isinstance(expr.type, _GenericAlias):
        return issubclass(get_origin(expr.type), ListObject)
    else:
        return issubclass(expr.type, ListObject)


def is_set_type_expr(expr: Expr) -> bool:
    if isinstance(expr.type, _GenericAlias):
        return issubclass(get_origin(expr.type), SetObject)
    else:
        return issubclass(expr.type, SetObject)


def is_tuple_type_expr(expr: Expr) -> bool:
    return isinstance(expr, TupleObject)


# Helper functions
def is_object_pointer_type(obj: NewObject) -> bool:
    return isinstance(obj, ListObject) or isinstance(obj, SetObject)
