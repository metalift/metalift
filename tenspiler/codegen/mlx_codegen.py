from typing import Any, Dict, Union

from metalift.ir import (
    Add,
    Call,
    Div,
    Eq,
    Expr,
    FnDecl,
    FnDeclRecursive,
    Ge,
    Gt,
    Le,
    Lit,
    Lt,
    Mod,
    Mul,
    Sub,
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
    def translate_fn_call(fn_name: str, *args: Any) -> str:
        processed_args = [helper(arg) for arg in args]
        if fn_name in {
            VEC_ELEMWISE_ADD,
            MATRIX_ELEMWISE_ADD,
            VEC_SCALAR_ADD,
            MATRIX_SCALAR_ADD,
        }:
            return f"torch.add({processed_args[0]}, {processed_args[1]})"
        elif fn_name in {
            VEC_ELEMWISE_SUB,
            MATRIX_ELEMWISE_SUB,
            SCALAR_VEC_SUB,
            SCALAR_MATRIX_SUB,
        }:
            return f"torch.sub({processed_args[0]}, {processed_args[1]})"
        elif fn_name in {VEC_SCALAR_SUB, MATRIX_SCALAR_SUB}:
            return f"torch.sub({processed_args[1]}, {processed_args[0]})"
        elif fn_name in {
            VEC_ELEMWISE_MUL,
            MATRIX_ELEMWISE_MUL,
            VEC_SCALAR_MUL,
            MATRIX_SCALAR_MUL,
        }:
            return f"torch.multiply({processed_args[0]}, {processed_args[1]})"
        elif fn_name in {
            VEC_ELEMWISE_DIV,
            MATRIX_ELEMWISE_DIV,
            SCALAR_VEC_DIV,
            SCALAR_MATRIX_DIV,
        }:
            # TODO: what do we do with integer division?
            return f"torch.divide({processed_args[0]}, {processed_args[1]})"
        elif fn_name in {VEC_SCALAR_DIV, MATRIX_SCALAR_DIV}:
            return f"torch.divide({processed_args[1]}, {processed_args[0]})"
        elif fn_name.endswith("matrix_selection_two_args"):
            for name, fn in all_synthesized_fns.items():
                if name.endswith("select_two_args"):
                    select_two_args_body = fn.body()
            if select_two_args_body is None:
                raise ValueError("select_two_args not found")
            cond = select_two_args_body.c()
            if_then = select_two_args_body.e1()
            if_else = select_two_args_body.e2()
            return f"torch.where({helper(cond)}, {helper(if_then)}, {helper(if_else)})"
        elif fn_name == "vec_map":
            map_fn_name = all_synthesized_fns[MAP_INT_TO_INT].body().name()
            if map_fn_name == "integer_sqrt":
                return f"torch.sqrt({processed_args[0]})"
            elif map_fn_name == "integer_exp":
                return f"torch.exp({processed_args[0]})"
            else:
                raise ValueError(f"Unknown map function name: {map_fn_name}")
        elif fn_name == "matrix_vec_mul":
            return f"torch.matmul({processed_args[0]}, {processed_args[1]})"
        # List access functions
        elif fn_name in {"list_take", "list_list_take"}:
            return f"{processed_args[0]}[:{processed_args[1]}]"
        elif fn_name in {"list_slice_with_length", "list_list_slice_with_length"}:
            return f"{processed_args[0]}[{processed_args[1]}:{processed_args[1]} + {processed_args[2]}]"
        elif fn_name == "list_list_col_slice_with_length":
            return f"{processed_args[0]}[:, {processed_args[1]}:{processed_args[1]} + {processed_args[2]}]"
        elif fn_name == "list_length":
            return f"{processed_args[0]}.size(dim=0)"
        # Matrix functions
        elif fn_name == "matrix_transpose":
            return f"torch.transpose({processed_args[0]}, 0, 1)"
        # Reduce functions
        elif fn_name == "reduce_max":
            return f"torch.max({processed_args[0]})"
        elif fn_name == "reduce_sum":
            return f"torch.sum({processed_args[0]})"
        elif fn_name == "reduce_mul":
            return f"torch.prod({processed_args[0]})"
        # Integer functions
        elif fn_name == "integer_sqrt":
            return f"torch.sqrt(torch.as_tensor({processed_args[0]}))"
        elif fn_name == "integer_exp":
            return f"torch.exp(torch.as_tensor({processed_args[0]}))"
        elif fn_name == MAP_INT_TO_INT:
            map_fn_name = all_synthesized_fns[MAP_INT_TO_INT].body().name()
            if map_fn_name == "integer_sqrt":
                return f"torch.sqrt(torch.as_tensor({processed_args[0]}))"
            elif map_fn_name == "integer_exp":
                return f"torch.exp(torch.as_tensor({processed_args[0]}))"
            else:
                raise ValueError(f"Unknown map function name: {map_fn_name}")
        raise Exception(f"Unknown function name: {fn_name}")

    def translate_non_fn_call(expr: Expr) -> str:
        processed_args = [helper(arg) for arg in expr.args]

        # Arithmetic operations
        if isinstance(expr, Add):
            return f"({processed_args[0]} + {processed_args[1]})"
        elif isinstance(expr, Sub):
            return f"({processed_args[0]} - {processed_args[1]})"
        elif isinstance(expr, Mul):
            return f"({processed_args[0]} * {processed_args[1]})"
        elif isinstance(expr, Div):
            op = "/" if d_type == DataType.FLOAT else "//"
            return f"({processed_args[0]} {op} {processed_args[1]})"
        elif isinstance(expr, Mod):
            return f"torch.greater({helper(expr.args[0])}, {helper(expr.args[1])})"

        # Comparison operations
        elif isinstance(expr, Gt):
            return f"torch.greater({processed_args[0]}, {processed_args[1]})"
        elif isinstance(expr, Ge):
            return f"torch.greater_equal({processed_args[0]}, {processed_args[1]})"
        elif isinstance(expr, Eq):
            return f"torch.eq({processed_args[0]}, {processed_args[1]})"
        elif isinstance(expr, Lt):
            return f"torch.less({processed_args[0]}, {processed_args[1]})"
        elif isinstance(expr, Le):
            return f"torch.less_equal({processed_args[0]}, {processed_args[1]})"
        elif isinstance(expr, Lit):
            return f"{expr.val()}"
        return str(expr)

    translations = {
        "vec_elemwise_add": lambda args: f"torch.add({helper(args[1])}, {helper(args[0])})",
        "vec_scalar_add": lambda args: f"torch.add({helper(args[1])}, {helper(args[0])})",
        "vec_elemwise_sub": lambda args: f"torch.sub({helper(args[1])}, {helper(args[0])})",
        "vec_elemwise_mul": lambda args: f"torch.multiply({helper(args[1])}, {helper(args[0])})",
        "vec_elemwise_div": lambda args: f"torch.divide({helper(args[1])}, {helper(args[0])})",
        "matrix_vec_mul": lambda args: f"torch.matmul({helper(args[0])}, {helper(args[1])})",
        "matrix_transpose": lambda args: f"torch.transpose({helper(args[0])}, 0, 1)",
        #### Which of the name is used for sqrt?
        "integer_sqrt": lambda args: f"torch.sqrt(torch.as_tensor({helper(args[0])}))",
        "vec_map": lambda args: f"torch.sqrt(torch.as_tensor({helper(args[0])}))"
        if helper(args[1]) == "integer_sqrt"
        else f"torch.exp({helper(args[0])})",
        "reduce_sum": lambda args: f"torch.sum({helper(args[0])})",
        "reduce_max": lambda args: f"torch.max({helper(args[0])})",
        "list_length": lambda args: f"{helper(args[0])}.size(dim=0)",
        "vec_scalar_mul": lambda args: f"torch.multiply({helper(args[0])}, {helper(args[1])})",
        "scalar_vec_div": lambda args: f"torch.divide({helper(args[0])}, {helper(args[1])})",
        "rand": lambda args: "torch.randint(1, 2147483647, base.shape, dtype=torch.int32, device='cuda')",
        "Ite": lambda args: f"torch.where({helper(args[0])}, {helper(args[1])}, {helper(args[2])})",
        "Lt": lambda args: f"torch.less({helper(args[0])}, {helper(args[1])})",
        "Le": lambda args: f"torch.less_equal({helper(args[0])}, {helper(args[1])})",
        "Gt": lambda args: f"torch.greater({helper(args[0])}, {helper(args[1])})",
        "Ge": lambda args: f"torch.greater_equal({helper(args[0])}, {helper(args[1])})",
        "Eq": lambda args: f"torch.eq({helper(args[0])}, {helper(args[1])})",
        # General for any of the frameworks
        "vec_scalar_sub": lambda args: f"{helper(args[1])} - {helper(args[0])}",
        "vec_scalar_div": lambda args: f"{helper(args[1])} / {helper(args[0])}",
        "vec_scalar_add": lambda args: f"{helper(args[1])} + {helper(args[0])}",
        "scalar_vec_sub": lambda args: f"{helper(args[0])} - {helper(args[1])}",
        # General for any python code
        "list_list_col_slice_with_length": lambda args: f"{helper(args[0])}[:, {helper(args[1])}:{helper(args[1])} + {args[2]}]",
        "list_slice_with_length": lambda args: f"{helper(args[0])}[{helper(args[1])}:{helper(args[1])} + {args[2]}]",
        "list_take": lambda args: f"{helper(args[0])}[:{helper(args[1])}]",
        "Div": lambda args: f"{helper(args[0])} / {helper(args[1])}"
        if d_type == DataType.FLOAT
        else f"{helper(args[0])} // {helper(args[1])}",
        "Mul": lambda args: f"{helper(args[0])} * {helper(args[1])}",
        "Sub": lambda args: f"{helper(args[0])} - {helper(args[1])}",
        "Add": lambda args: f"{helper(args[0])} + {helper(args[1])}",
        "Mod": lambda args: f"{helper(args[0])} % {helper(args[1])}",
        "And": lambda args: " and ".join(helper(a) for a in args),
        "Or": lambda args: " or ".join(helper(a) for a in args),
        "Not": lambda args: f"not {helper(args[0])}",
        "vec_map": {
            "integer_exp": lambda args: f"torch.exp({helper(args[0])})",
            "integer_sqrt": lambda args: f"torch.sqrt({helper(args[0])})",
        },
    }
    vars_to_replace = {"int_x": "base", "int_y": "active"}

    def helper(expr):
        if isinstance(expr, Call):
            return translate_fn_call(expr.name(), *expr.arguments())
        elif isinstance(expr, Expr):
            return translate_non_fn_call(expr)
        else:
            return str(expr)
        # elif isinstance(expr, Lit):
        #     return f"{expr.val()}"
        # elif expr.__class__.__name__ in translations.keys():
        #     return translations[expr.__class__.__name__](expr.args)
        # else:
        #     name = "%s" % (expr)
        #     return vars_to_replace.get(name, name)

    return helper(ps_fn_decl.body())
