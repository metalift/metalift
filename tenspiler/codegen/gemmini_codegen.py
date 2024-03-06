# normal_blend_8/f screen_blend/matmul rms_norm1 softmax3
# linear_burn/dodge

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
    List as mlList,
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


def gemmini_codegen(
    ps_fn_decl: Union[FnDecl, FnDeclRecursive],
    all_synthesized_fns: Dict[str, Expr],
    d_type: DataType = DataType.FLOAT,
) -> str:
    def helper(expr: Any, vars_to_replace: Dict[str, Expr] = {}, curr_var: str = "") -> Tuple[str, ObjectT]:
        if not isinstance(expr, Expr):
            return str(expr), None
        if isinstance(expr, Call):
            # processed_args = [
            #     helper(arg, vars_to_replace)[0] for arg in expr.arguments()
            # ]
            fn_name = expr.name()
            if fn_name == VEC_ELEMWISE_ADD:
                args = expr.arguments()
                if isinstance(args[0], Call) and isinstance(args[1], Call) and args[0].name() == VEC_SCALAR_MUL and args[1].name() == VEC_SCALAR_MUL:
                        
                        expr1_args = [
                            helper(arg, vars_to_replace)[0] for arg in args[0].arguments()
                        ]
                        expr2_args = [
                            helper(arg, vars_to_replace)[0] for arg in args[1].arguments()
                        ]
                        return f"tiled_resadd_auto(LEN, LEN, {expr1_args[0]}, {expr2_args[0]}, 1, {expr1_args[1]}[0], {expr2_args[1]}[0], {curr_var}[0], false, WS);", expr.type
            elif fn_name == MATRIX_ELEMWISE_ADD:
                processed_args = [
                    helper(arg, vars_to_replace)[0] for arg in expr.arguments()
                ]
                return f"tiled_resadd_auto(LEN, LEN, 1, 1, 1, {processed_args[0]}[0], {processed_args[1]}[0], {curr_var}[0], false, WS);", expr.type
            elif fn_name == VEC_ELEMWISE_MUL:
                processed_args = [
                    helper(arg, vars_to_replace)[0] for arg in expr.arguments()
                ]
                return (
                      f"for (int i = 0; i < LEN; i++) {{ {curr_var}[0][i] = {processed_args[0]}[0][i] * {processed_args[1]}[0][i]; }}",
                    expr.type,
                )
            elif fn_name == "matrix_vec_mul":
                processed_args = [
                    helper(arg, vars_to_replace)[0] for arg in expr.arguments()
                ]
                return (
                    f"tiled_matmul_auto(LEN, LEN, 1, (elem_t*) {processed_args[0]}, (elem_t*) {processed_args[1]}, NULL, (elem_t*){curr_var}, 1, LEN, LEN, LEN, 1, 1, 1, 0, 1, 0, false, false, false, false, 0, 0,WS);",
                    expr.type,
                )
            elif fn_name == "list_take":
                processed_args = [
                    helper(arg, vars_to_replace)[0] for arg in expr.arguments()
                ]
                return f"for (int i = 0; i < {processed_args[1]}; i++) {{ {curr_var}[0][i] = {processed_args[0]}[0][i]; }}", expr.type
            elif fn_name == "reduce_sum":
                arg = expr.arguments()[0]
                res = ""
                if isinstance(arg, Call):
                    intermediate_var = "interm"
                    #input to reduce_sum has to be list of integer. to represent in gemmini, we use 1xlen matrix
                    interm_var_def = f"static elem_t {intermediate_var}[1][LEN];"
                    res += interm_var_def

                    interm_code = helper(arg, vars_to_replace, intermediate_var)[0]
                    res += interm_code
                else:
                    intermediate_var = helper(arg, vars_to_replace)[0]

                expanded_var = "unflat"
                expanded_var_def = f"static elem_t {expanded_var}[LEN][LEN];"
                res += expanded_var_def
                res += f"int v = 0; for (int i = 0; i < LEN; i++) {{ for (int j = 0; j < LEN; j++) {{ {expanded_var}[i][j] = {intermediate_var}[0][v]; v++;}} }}"

                input_arg = expanded_var if isinstance(arg, Call) else helper(arg, vars_to_replace)[0]
                res += f"tiled_global_average({input_arg}[0], {curr_var}, 1, 1, LEN, 1);"
                return res, expr.type

        # Arithmetic operations
        processed_args = [helper(arg, vars_to_replace) for arg in expr.args]
        processed_args_types = [a[1] for a in processed_args]
        processed_args = [a[0] for a in processed_args]
        if any(isinstance(expr, cls) for cls in [Add, Sub, Mul, Div, Mod]):
            is_arg_type_int = all([a_type is Int for a_type in processed_args_types])
            if is_arg_type_int:
                if isinstance(expr, Add):
                    return f"({processed_args[0]} + {processed_args[1]})", Int
                elif isinstance(expr, Sub):
                    return f"({processed_args[0]} - {processed_args[1]})", Int
                elif isinstance(expr, Mul):
                    return f"({processed_args[0]} * {processed_args[1]})", Int
                elif isinstance(expr, Mod):
                    return f"({processed_args[0]} % {processed_args[1]})", Int
                else:
                    op = "/" if d_type == DataType.FLOAT else "//"
                    return f"({processed_args[0]} {op} {processed_args[1]})", Int
            raise Exception(f"Arithmatic of non-integer type")

        # Other
        elif isinstance(expr, Lit):
            return f"{expr.val()}", expr.type
        elif isinstance(expr, Var):
            if expr.name() in vars_to_replace:
                return helper(vars_to_replace[expr.name()], vars_to_replace)
            return expr.name(), expr.type
        return str(expr)

    return helper(ps_fn_decl.body(), {}, "out")[0]
