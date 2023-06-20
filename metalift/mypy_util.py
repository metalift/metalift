from mypy.nodes import CallExpr, NameExpr, MemberExpr
from typing import cast


def is_func_call(o: CallExpr) -> bool:
    return isinstance(o.callee, NameExpr)


def is_func_call_with_name(o: CallExpr, func_name: str) -> bool:
    return is_func_call(o) and cast(NameExpr, o.callee).name == func_name


def is_method_call_with_name(o: CallExpr, method_name: str) -> bool:
    return isinstance(o.callee, MemberExpr) and o.callee.name == method_name
