from typing import Union
import typing
from metalift.ir import Expr, ListObject, NewObject, SetObject
import metalift.ir as ir

#TODO(jie): change it to MLType = typing.Type["NewObject"] when all Type has removed
MLType = Union[ir.Type, typing.Type["NewObject"]]

def is_list_type_expr(expr: Expr) -> bool:
    return expr.type.cls_str() == "List"

def is_set_type_expr(expr: Expr) -> bool:
    return expr.type.cls_str() == "Set"

def is_tuple_type_expr(expr: Expr) -> bool:
    return expr.type.cls_str() == "Tuple"


# Helper functions
def is_type_pointer(ty: MLType) -> bool:
    return (
        hasattr(ty, "__origin__") and ty.__origin__ in {ListObject, SetObject}
    )
