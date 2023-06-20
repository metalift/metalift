from metalift.ir import Expr


def is_list_type_expr(expr: Expr) -> bool:
    return expr.type.name == "MLList"
