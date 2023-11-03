from typing import _GenericAlias, get_origin  # type: ignore
from metalift.ir import (
    Expr,
    ListObject,
    NewObject,
    SetObject,
    TupleObject,
)


def is_list_type_expr(expr: Expr) -> bool:
    if isinstance(expr.type, _GenericAlias):
        return issubclass(get_origin(expr.type), ListObject)  # type: ignore
    else:
        return issubclass(expr.type, ListObject)


def is_set_type_expr(expr: Expr) -> bool:
    if isinstance(expr.type, _GenericAlias):
        return issubclass(get_origin(expr.type), SetObject)  # type: ignore
    else:
        return issubclass(expr.type, SetObject)


def is_tuple_type_expr(expr: Expr) -> bool:
    return isinstance(expr, TupleObject)


# Helper functions
def is_object_pointer_type(obj: NewObject) -> bool:
    return isinstance(obj, ListObject) or isinstance(obj, SetObject)
