from typing import Any, Dict, Tuple, Union

from metalift.ir import (
    Add,
    Bool,
    Call,
    Div,
    Eq,
    Expr,
    FnDecl,
    FnDeclRecursive,
    Ge,
    Gt,
    Int,
    Le,
    Lit,
    Lt,
    Mod,
    Mul,
    Not,
    ObjectT,
    Sub,
    Var,
)
from tenspiler.codegen.utils import DataType
from tenspiler.tenspiler_common import (
    MAP_INT_TO_INT,
    MATRIX_ELEMWISE_ADD,
    MATRIX_ELEMWISE_DIV,
    MATRIX_ELEMWISE_MUL,
    MATRIX_ELEMWISE_SUB,
    MATRIX_SCALAR_ADD,
    MATRIX_SCALAR_DIV,
    MATRIX_SCALAR_MUL,
    MATRIX_SCALAR_SUB,
    SCALAR_MATRIX_DIV,
    SCALAR_MATRIX_SUB,
    SCALAR_VEC_DIV,
    SCALAR_VEC_SUB,
    VEC_ELEMWISE_ADD,
    VEC_ELEMWISE_DIV,
    VEC_ELEMWISE_MUL,
    VEC_ELEMWISE_SUB,
    VEC_SCALAR_ADD,
    VEC_SCALAR_DIV,
    VEC_SCALAR_MUL,
    VEC_SCALAR_SUB,
)


def mlx_codegen(
    ps_fn_decl: Union[FnDecl, FnDeclRecursive],
    all_synthesized_fns: Dict[str, Expr],
    d_type: DataType = DataType.FLOAT,
) -> str:
    def helper(expr: Any, vars_to_replace: Dict[str, Expr] = {}) -> Tuple[str, ObjectT]:
        if not isinstance(expr, Expr):
            return str(expr), None
        if isinstance(expr, Call):
            processed_args = [
                helper(arg, vars_to_replace)[0] for arg in expr.arguments()
            ]
            fn_name = expr.name()
            if fn_name in {
                VEC_ELEMWISE_ADD,
                MATRIX_ELEMWISE_ADD,
                VEC_SCALAR_ADD,
                MATRIX_SCALAR_ADD,
            }:
                return f"torch.add({processed_args[0]}, {processed_args[1]})", expr.type
            elif fn_name in {
                VEC_ELEMWISE_SUB,
                MATRIX_ELEMWISE_SUB,
                SCALAR_VEC_SUB,
                SCALAR_MATRIX_SUB,
            }:
                return f"torch.sub({processed_args[0]}, {processed_args[1]})", expr.type
            elif fn_name in {VEC_SCALAR_SUB, MATRIX_SCALAR_SUB}:
                return f"torch.sub({processed_args[1]}, {processed_args[0]})", expr.type
            elif fn_name in {
                VEC_ELEMWISE_MUL,
                MATRIX_ELEMWISE_MUL,
                VEC_SCALAR_MUL,
                MATRIX_SCALAR_MUL,
            }:
                return (
                    f"torch.multiply({processed_args[0]}, {processed_args[1]})",
                    expr.type,
                )
            elif fn_name in {
                VEC_ELEMWISE_DIV,
                MATRIX_ELEMWISE_DIV,
                SCALAR_VEC_DIV,
                SCALAR_MATRIX_DIV,
            }:
                # TODO: what do we do with integer division?
                return (
                    f"torch.divide({processed_args[0]}, {processed_args[1]})",
                    expr.type,
                )
            elif fn_name in {VEC_SCALAR_DIV, MATRIX_SCALAR_DIV}:
                return (
                    f"torch.divide({processed_args[1]}, {processed_args[0]})",
                    expr.type,
                )
            elif fn_name.endswith("matrix_selection_two_args"):
                for name, fn in all_synthesized_fns.items():
                    if name.endswith("select_two_args"):
                        select_two_args_fn_decl = fn
                if select_two_args_fn_decl is None:
                    raise ValueError("select_two_args not found")
                select_two_args_body = select_two_args_fn_decl.body()
                cond = select_two_args_body.c()
                if_then = select_two_args_body.e1()
                if_else = select_two_args_body.e2()
                select_args = select_two_args_fn_decl.arguments()[:2]
                matrix_args = expr.arguments()[:2]
                vars_to_replace: Dict[str, Expr] = {}
                for i in range(2):
                    vars_to_replace[select_args[i].name()] = matrix_args[i]
                return (
                    f"torch.where({helper(cond, vars_to_replace)[0]}, {helper(if_then, vars_to_replace)[0]}, {helper(if_else, vars_to_replace)[0]})",
                    expr.type,
                )
            elif fn_name == "vec_map":
                map_fn_name = all_synthesized_fns[MAP_INT_TO_INT].body().name()
                if map_fn_name == "integer_sqrt":
                    return f"torch.sqrt({processed_args[0]})", expr.type
                elif map_fn_name == "integer_exp":
                    return f"torch.exp({processed_args[0]})", expr.type
                else:
                    raise ValueError(f"Unknown map function name: {map_fn_name}")
            elif fn_name == "matrix_vec_mul":
                return (
                    f"torch.matmul({processed_args[0]}, {processed_args[1]})",
                    expr.type,
                )
            # List access functions
            elif fn_name == "list_eq":
                return (
                    f"torch.all(torch.eq({processed_args[0]}, {processed_args[1]})).item()",
                    expr.type,
                )
            elif fn_name == "list_empty":
                return f"torch.empty(0)", expr.type
            elif fn_name == "list_list_empty":
                return f"torch.empty(0, 0)", expr.type
            elif fn_name in {"list_get", "list_list_get"}:
                return f"{processed_args[0]}[{processed_args[1]}]", expr.type
            elif fn_name in {"list_append", "list_list_append"}:
                return (
                    f"torch.cat([{processed_args[0]}, {processed_args[1]}.unsqueeze(0)], dim=0)",
                    expr.type,
                )
            elif fn_name in {"list_prepend", "list_list_prepend"}:
                return (
                    f"torch.cat([{processed_args[1].unsqueeze(0)}, {processed_args[0]}], dim=0)",
                    expr.type,
                )
            elif fn_name == "list_concat":
                return (
                    f"torch.cat([{processed_args[0]}, {processed_args[1]}], dim=0)",
                    expr.type,
                )
            elif fn_name in {"list_tail", "list_list_tail"}:
                return f"{processed_args[0]}[{processed_args[1]}:]", expr.type
            elif fn_name in {"list_take", "list_list_take"}:
                return f"{processed_args[0]}[:{processed_args[1]}]", expr.type
            elif fn_name in {"list_slice", "list_list_slice"}:
                return (
                    f"{processed_args[0]}[{processed_args[1]}:{processed_args[2]}]",
                    expr.type,
                )
            elif fn_name in {"list_slice_with_length", "list_list_slice_with_length"}:
                return (
                    f"{processed_args[0]}[{processed_args[1]}:{processed_args[1]} + {processed_args[2]}]",
                    expr.type,
                )
            elif fn_name == "list_list_col_slice":
                return (
                    f"{processed_args[0]}[:, {processed_args[1]}:{processed_args[2]}]",
                    expr.type,
                )
            elif fn_name == "list_list_col_slice_with_length":
                return (
                    f"{processed_args[0]}[:, {processed_args[1]}:{processed_args[1]} + {processed_args[2]}]",
                    expr.type,
                )
            elif fn_name in {"list_length", "list_list_length"}:
                return f"{processed_args[0]}.size(dim=0)", expr.type
            # Matrix functions
            elif fn_name == "matrix_transpose":
                return f"torch.transpose({processed_args[0]}, 0, 1)", expr.type
            # Reduce functions
            elif fn_name == "reduce_max":
                return f"torch.max({processed_args[0]}).item()", expr.type
            elif fn_name == "reduce_sum":
                return f"torch.sum({processed_args[0]}).item()", expr.type
            elif fn_name == "reduce_mul":
                return f"torch.prod({processed_args[0]}).item()", expr.type
            # Integer functions
            elif fn_name == "integer_sqrt":
                return (
                    f"torch.sqrt(torch.as_tensor({processed_args[0]})).item()",
                    expr.type,
                )
            elif fn_name == "integer_exp":
                return (
                    f"torch.exp(torch.as_tensor({processed_args[0]})).item()",
                    expr.type,
                )
            elif fn_name == MAP_INT_TO_INT:
                map_fn_name = all_synthesized_fns[MAP_INT_TO_INT].body().name()
                if map_fn_name == "integer_sqrt":
                    return (
                        f"torch.sqrt(torch.as_tensor({processed_args[0]}))",
                        expr.type,
                    )
                elif map_fn_name == "integer_exp":
                    return f"torch.exp(torch.as_tensor({processed_args[0]}))", expr.type
                else:
                    raise ValueError(f"Unknown map function name: {map_fn_name}")
            raise Exception(f"Unknown function name: {fn_name}")

        # Arithmetic operations
        processed_args = [helper(arg, vars_to_replace) for arg in expr.args]
        processed_args_types = [a[1] for a in processed_args]
        processed_args = [a[0] for a in processed_args]
        if any(isinstance(expr, cls) for cls in [Add, Sub, Mul, Div]):
            is_arg_type_int = all([a_type is Int for a_type in processed_args_types])
            if is_arg_type_int:
                if isinstance(expr, Add):
                    return f"({processed_args[0]} + {processed_args[1]})", Int
                elif isinstance(expr, Sub):
                    return f"({processed_args[0]} - {processed_args[1]})", Int
                elif isinstance(expr, Mul):
                    return f"({processed_args[0]} * {processed_args[1]})", Int
                else:
                    op = "/" if d_type == DataType.FLOAT else "//"
                    return f"({processed_args[0]} {op} {processed_args[1]})", Int
            else:
                non_int_arg_types = [
                    a_type
                    for a_type in processed_args_types
                    if a_type is not Int and a_type is not None
                ]
                ret_type = non_int_arg_types[0]
                if isinstance(expr, Add):
                    return (
                        f"torch.add({processed_args[0]}, {processed_args[1]})",
                        ret_type,
                    )
                elif isinstance(expr, Sub):
                    return (
                        f"torch.sub({processed_args[0]}, {processed_args[1]})",
                        ret_type,
                    )
                elif isinstance(expr, Mul):
                    return (
                        f"torch.multiply({processed_args[0]}, {processed_args[1]})",
                        ret_type,
                    )
                else:
                    return (
                        f"torch.divide({processed_args[0]}, {processed_args[1]})",
                        ret_type,
                    )
        elif isinstance(expr, Mod):
            return f"({processed_args[0]} % {processed_args[1]})", ret_type

        # Relational operations
        elif any(isinstance(expr, cls) for cls in [Gt, Ge, Eq, Lt, Le, Not]):
            is_arg_type_int = all([a_type is Int for a_type in processed_args_types])
            if is_arg_type_int:
                if isinstance(expr, Eq):
                    return f"({processed_args[0]} == {processed_args[1]})", Bool
                elif isinstance(expr, Gt):
                    return f"({processed_args[0]} > {processed_args[1]})", Bool
                elif isinstance(expr, Ge):
                    return f"({processed_args[0]} >= {processed_args[1]})", Bool
                elif isinstance(expr, Lt):
                    return f"({processed_args[0]} < {processed_args[1]})", Bool
                elif isinstance(expr, Le):
                    return f"({processed_args[0]} <= {processed_args[1]})", Bool
                else:
                    return f"not {processed_args[0]}", Bool
            else:
                non_int_arg_types = [
                    a_type
                    for a_type in processed_args_types
                    if a_type is not Int and a_type is not None
                ]
                ret_type = non_int_arg_types[0]
                if isinstance(expr, Eq):
                    return (
                        f"torch.eq({processed_args[0]}, {processed_args[1]})",
                        ret_type,
                    )
                elif isinstance(expr, Gt):
                    return (
                        f"torch.greater({processed_args[0]}, {processed_args[1]})",
                        ret_type,
                    )
                elif isinstance(expr, Ge):
                    return (
                        f"torch.greater_equal({processed_args[0]}, {processed_args[1]})",
                        ret_type,
                    )
                elif isinstance(expr, Lt):
                    return (
                        f"torch.less({processed_args[0]}, {processed_args[1]})",
                        ret_type,
                    )
                elif isinstance(expr, Le):
                    return (
                        f"torch.less_equal({processed_args[0]}, {processed_args[1]})",
                        ret_type,
                    )
                else:
                    return f"torch.logical_not({processed_args[0]})", ret_type

        # Other
        elif isinstance(expr, Lit):
            return f"{expr.val()}", expr.type
        elif isinstance(expr, Var):
            if expr.name() in vars_to_replace:
                return helper(vars_to_replace[expr.name()], vars_to_replace)
            return expr.name(), expr.type
        return str(expr)

    return helper(ps_fn_decl.body())[0]
