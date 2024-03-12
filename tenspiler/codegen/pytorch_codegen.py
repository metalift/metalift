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
    And,
    Or,
    List as mlList
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

translations = {
    # VEC_ELEMWISE_ADD: lambda processed_args: f"torch.add({processed_args[0]}, {processed_args[1]})",
    # MATRIX_ELEMWISE_ADD: lambda processed_args: f"torch.add({processed_args[0]}, {processed_args[1]})",
    # VEC_SCALAR_ADD: lambda processed_args: f"torch.add({processed_args[0]}, {processed_args[1]})",
    # MATRIX_SCALAR_ADD: lambda processed_args: f"torch.add({processed_args[0]}, {processed_args[1]})",

    VEC_ELEMWISE_ADD: lambda processed_args: f"({processed_args[0]}) + ({processed_args[1]})",
    MATRIX_ELEMWISE_ADD: lambda processed_args: f"({processed_args[0]}) + ({processed_args[1]})",
    VEC_SCALAR_ADD: lambda processed_args:  f"({processed_args[0]}) + ({processed_args[1]})",
    MATRIX_SCALAR_ADD: lambda processed_args:  f"({processed_args[0]}) + ({processed_args[1]})",

    # VEC_ELEMWISE_SUB: lambda processed_args: f"torch.sub({processed_args[0]}, {processed_args[1]})",
    # MATRIX_ELEMWISE_SUB: lambda processed_args: f"torch.sub({processed_args[0]}, {processed_args[1]})",
    # SCALAR_VEC_SUB: lambda processed_args: f"torch.sub({processed_args[0]}, {processed_args[1]})",
    # SCALAR_MATRIX_SUB: lambda processed_args: f"torch.sub({processed_args[0]}, {processed_args[1]})",

    VEC_ELEMWISE_SUB: lambda processed_args: f"({processed_args[0]}) - ({processed_args[1]})",
    MATRIX_ELEMWISE_SUB: lambda processed_args: f"({processed_args[0]}) - ({processed_args[1]})",
    SCALAR_VEC_SUB: lambda processed_args: f"({processed_args[0]}) - ({processed_args[1]})",
    SCALAR_MATRIX_SUB: lambda processed_args: f"({processed_args[0]}) - ({processed_args[1]})",

    # VEC_SCALAR_SUB: lambda processed_args: f"torch.sub({processed_args[1]}, {processed_args[0]})",
    # MATRIX_SCALAR_SUB: lambda processed_args: f"torch.sub({processed_args[1]}, {processed_args[0]})",
    VEC_SCALAR_SUB: lambda processed_args: f"({processed_args[1]}) - ({processed_args[0]})",
    MATRIX_SCALAR_SUB: lambda processed_args: f"({processed_args[1]}) - ({processed_args[0]})",

    # VEC_ELEMWISE_MUL: lambda processed_args: f"torch.multiply({processed_args[0]}, {processed_args[1]})",
    # MATRIX_ELEMWISE_MUL: lambda processed_args: f"torch.multiply({processed_args[0]}, {processed_args[1]})",
    # VEC_SCALAR_MUL: lambda processed_args: f"torch.multiply({processed_args[0]}, {processed_args[1]})",
    # MATRIX_SCALAR_MUL: lambda processed_args: f"torch.multiply({processed_args[0]}, {processed_args[1]})",

    VEC_ELEMWISE_MUL: lambda processed_args: f"({processed_args[0]}) * ({processed_args[1]})",
    MATRIX_ELEMWISE_MUL: lambda processed_args: f"({processed_args[0]}) * ({processed_args[1]})",
    VEC_SCALAR_MUL: lambda processed_args: f"({processed_args[0]}) * ({processed_args[1]})",
    MATRIX_SCALAR_MUL: lambda processed_args: f"({processed_args[0]}) * ({processed_args[1]})",

    # VEC_ELEMWISE_DIV: lambda processed_args: f"torch.divide({processed_args[0]}, {processed_args[1]})",
    # MATRIX_ELEMWISE_DIV: lambda processed_args: f"torch.divide({processed_args[0]}, {processed_args[1]})",
    # SCALAR_VEC_DIV: lambda processed_args: f"torch.divide({processed_args[0]}, {processed_args[1]})",
    # SCALAR_MATRIX_DIV: lambda processed_args: f"torch.divide({processed_args[0]}, {processed_args[1]})",
    VEC_ELEMWISE_DIV: lambda processed_args, is_floor: f"({processed_args[0]}) // ({processed_args[1]})" if is_floor else f"({processed_args[0]}) / ({processed_args[1]})",
    MATRIX_ELEMWISE_DIV: lambda processed_args, is_floor: f"({processed_args[0]}) // ({processed_args[1]})" if is_floor else f"({processed_args[0]}) / ({processed_args[1]})",
    SCALAR_VEC_DIV: lambda processed_args, is_floor: f"({processed_args[0]}) // ({processed_args[1]})" if is_floor else f"({processed_args[0]}) / ({processed_args[1]})",
    SCALAR_MATRIX_DIV: lambda processed_args, is_floor: f"({processed_args[0]}) // ({processed_args[1]})" if is_floor else f"({processed_args[0]}) / ({processed_args[1]})",

    # VEC_SCALAR_DIV: lambda processed_args: f"torch.divide({processed_args[1]}, {processed_args[0]})",
    # MATRIX_SCALAR_DIV: lambda processed_args: f"torch.divide({processed_args[1]}, {processed_args[0]})",
    VEC_SCALAR_DIV: lambda processed_args, is_floor: f"({processed_args[1]}) // ({processed_args[0]})" if is_floor else f"({processed_args[1]}) / ({processed_args[0]})",
    MATRIX_SCALAR_DIV: lambda processed_args, is_floor: f"({processed_args[1]}) // ({processed_args[0]})" if is_floor else f"({processed_args[1]}) / ({processed_args[0]})",

    "matrix_vec_mul": lambda processed_args: f"torch.matmul({processed_args[0]}, {processed_args[1]})",
    "list_eq": lambda processed_args: f"torch.all(torch.eq({processed_args[0]}, {processed_args[1]}))",

    "list_empty": lambda processed_args: f"torch.empty(0)",
    "list_list_empty": lambda processed_args: f"torch.empty(0, 0)",

    "list_get": lambda processed_args: f"{processed_args[0]}[{processed_args[1]}]",
    "list_list_get": lambda processed_args: f"{processed_args[0]}[{processed_args[1]}]",

    "list_append": lambda processed_args: f"torch.cat([{processed_args[0]}, {processed_args[1]}.unsqueeze(0)], dim=0)",
    "list_list_append": lambda processed_args: f"torch.cat([{processed_args[0]}, {processed_args[1]}.unsqueeze(0)], dim=0)",


    "list_prepend": lambda processed_args: f"torch.cat([{processed_args[1].unsqueeze(0)}, {processed_args[0]}], dim=0)",
    "list_list_prepend": lambda processed_args: f"torch.cat([{processed_args[1].unsqueeze(0)}, {processed_args[0]}], dim=0)",

    "list_concat": lambda processed_args: f"torch.cat([{processed_args[0]}, {processed_args[1]}], dim=0)",

    "list_tail": lambda processed_args: f"{processed_args[0]}[:{processed_args[1]}]",
    "list_list_tail" : lambda processed_args: f"{processed_args[0]}[{processed_args[1]}:]",

    "list_take": lambda processed_args: f"{processed_args[0]}[:{processed_args[1]}]",
    "list_list_take": lambda processed_args: f"{processed_args[0]}[:{processed_args[1]}]",

    "list_slice": lambda processed_args: f"{processed_args[0]}[{processed_args[1]}:{processed_args[2]}]",
    "list_list_slice": lambda processed_args: f"{processed_args[0]}[{processed_args[1]}:{processed_args[2]}]",

    "list_slice_with_length": lambda processed_args: f"{processed_args[0]}[{processed_args[1]}:{processed_args[1]} + {processed_args[2]}]",
    "list_list_slice_with_length": lambda processed_args: f"{processed_args[0]}[{processed_args[1]}:{processed_args[1]} + {processed_args[2]}]",

    "list_list_col_slice": lambda processed_args: f"{processed_args[0]}[:, {processed_args[1]}:{processed_args[2]}]",

    "list_list_col_slice_with_length": lambda processed_args: f"{processed_args[0]}[:, {processed_args[1]}:{processed_args[1]} + {processed_args[2]}]",

    "list_length": lambda processed_args: f"{processed_args[0]}.size(dim=0)",
    "list_list_length": lambda processed_args: f"{processed_args[0]}.size(dim=0)",

    "matrix_transpose": lambda processed_args: f"torch.transpose({processed_args[0]}, 0, 1)",

    "reduce_max": lambda processed_args: f"torch.max({processed_args[0]})",

    "reduce_sum": lambda processed_args: f"torch.sum({processed_args[0]})",

    "reduce_mul": lambda processed_args: f"torch.prod({processed_args[0]})",

    "integer_sqrt": lambda processed_args, is_list=False: f"torch.sqrt(torch.as_tensor({processed_args[0]}))",

    "integer_exp": lambda processed_args, is_list=False: f"torch.exp(torch.as_tensor({processed_args[0]}))",

    # Add: lambda processed_args, is_int: f"{processed_args[0]} + {processed_args[1]}" if is_int else f"torch.add({processed_args[0]}, {processed_args[1]})",
    # Sub: lambda processed_args, is_int: f"{processed_args[0]} - {processed_args[1]}" if is_int else f"torch.sub({processed_args[0]}, {processed_args[1]})",
    # Mul: lambda processed_args, is_int: f"{processed_args[0]} * {processed_args[1]}" if is_int else f"torch.multiply({processed_args[0]}, {processed_args[1]})",
    # Div: lambda processed_args, is_int: f"{processed_args[0]} // {processed_args[1]}" if is_int else f"torch.divide({processed_args[0]}, {processed_args[1]})",
    Add: lambda processed_args, is_int: f"({processed_args[0]}) + ({processed_args[1]})",
    Sub: lambda processed_args, is_int: f"({processed_args[0]}) - ({processed_args[1]})",
    Mul: lambda processed_args, is_int: f"({processed_args[0]}) * ({processed_args[1]})",
    Div: lambda processed_args, is_int: f"({processed_args[0]}) // ({processed_args[1]})",
    "float_div": lambda processed_args: f"({processed_args[0]}) / ({processed_args[1]})",
    Mod: lambda processed_args, is_int: f"({processed_args[0]}) % ({processed_args[1]})",

    Eq: lambda processed_args, is_int: f"{processed_args[0]} == {processed_args[1]}" if is_int else f"torch.eq({processed_args[0]}, {processed_args[1]})",
    Gt: lambda processed_args, is_int: f"{processed_args[0]} > {processed_args[1]}" if is_int else f"torch.greater({processed_args[0]}, {processed_args[1]})",
    Ge: lambda processed_args, is_int: f"{processed_args[0]} >= {processed_args[1]}" if is_int else f"torch.greater_equal({processed_args[0]}, {processed_args[1]})",
    Lt: lambda processed_args, is_int: f"{processed_args[0]} < {processed_args[1]}" if is_int else f"torch.less({processed_args[0]}, {processed_args[1]})",
    Le: lambda processed_args, is_int: f"{processed_args[0]} <= {processed_args[1]}" if is_int else f"torch.less_equal({processed_args[0]}, {processed_args[1]})",

    Not: lambda processed_args, is_prim: f"not {processed_args[0]}" if is_prim else f"torch.logical_not({processed_args[0]})",
    And: lambda processed_args, is_prim: f"({processed_args[0]}) and ({processed_args[1]})" if is_prim else f"torch.logical_and({processed_args[0]}, {processed_args[1]})",
    Or: lambda processed_args, is_prim: f"({processed_args[0]}) or ({processed_args[1]})" if is_prim else f"torch.logical_or({processed_args[0]}, {processed_args[1]})",
}

def pytorch_codegen(
    ps_fn_decl: Union[FnDecl, FnDeclRecursive],
    all_synthesized_fns: Dict[str, Expr],
    d_type: DataType = DataType.FLOAT,
) -> str:
    def helper(expr: Any, vars_to_replace: Dict[str, Expr] = {}) -> Tuple[str, ObjectT]:
        if not isinstance(expr, Expr):
            return str(expr), None
        if isinstance(expr, Call):
            processed_args = [helper(arg, vars_to_replace)[0] for arg in expr.arguments()]
            fn_name = expr.name()
            if fn_name.endswith("matrix_selection_two_args"):
                for name, fn in all_synthesized_fns.items():
                    if name.endswith("select_two_args"):
                        select_two_args_fn_decl = fn
                if select_two_args_fn_decl is None:
                    raise ValueError("select_two_args not found")
                select_two_args_body = select_two_args_fn_decl.body()
                cond, if_then, if_else = select_two_args_body.c(), select_two_args_body.e1(), select_two_args_body.e2()
                select_args = select_two_args_fn_decl.arguments()[:2]
                matrix_args = expr.arguments()[:2]
                vars_to_replace: Dict[str, Expr] = {}
                for i in range(2):
                    vars_to_replace[select_args[i].name()] = matrix_args[i]
                return (f"torch.where({helper(cond, vars_to_replace)[0]}, {helper(if_then, vars_to_replace)[0]}, {helper(if_else, vars_to_replace)[0]})", expr.type,)
            elif fn_name == MAP_INT_TO_INT or fn_name == "vec_map":
                map_fn_name = all_synthesized_fns[MAP_INT_TO_INT].body().name()
                if map_fn_name in {"integer_sqrt", "integer_exp"}:
                    return translations[map_fn_name](processed_args, fn_name == "vec_map"), expr.type
                else:
                    raise ValueError(f"Unknown map function name: {map_fn_name}")
            elif fn_name in translations.keys():
                if fn_name in {VEC_ELEMWISE_DIV, MATRIX_ELEMWISE_DIV, SCALAR_VEC_DIV, SCALAR_MATRIX_DIV, VEC_SCALAR_DIV, MATRIX_SCALAR_DIV}:
                    return translations[fn_name](processed_args, d_type == DataType.INT), expr.type
                return translations[fn_name](processed_args), expr.type
            raise Exception(f"Unknown function name: {fn_name}")    

        # Arithmetic operations
        processed_args = [helper(arg, vars_to_replace) for arg in expr.args]
        processed_args_types = [a[1] for a in processed_args]
        processed_args = [a[0] for a in processed_args]
        if any(isinstance(expr, cls) for cls in [Add, Sub, Mul, Div, Mod]):
            is_arg_type_int = all([a_type is Int for a_type in processed_args_types])
            ret_type = Int if is_arg_type_int else [a_type for a_type in processed_args_types if a_type is not Int and a_type is not None][0]
            if isinstance(expr, Div) and d_type == DataType.FLOAT:
                return translations["float_div"](processed_args), ret_type
            return translations[type(expr)](processed_args, is_arg_type_int), ret_type

        # Relational operations
        elif any(isinstance(expr, cls) for cls in [Gt, Ge, Eq, Lt, Le]):
            is_arg_type_int = all([a_type is Int for a_type in processed_args_types])
            ret_type = Bool if is_arg_type_int else mlList[Bool]
            return translations[type(expr)](processed_args, is_arg_type_int), ret_type
        elif any(isinstance(expr, cls) for cls in [And, Or, Not]):
            is_arg_type_prim = all([a_type is Int or a_type is Bool for a_type in processed_args_types])
            ret_type = Bool if is_arg_type_prim else mlList[Bool]
            return translations[type(expr)](processed_args, is_arg_type_prim), ret_type
        
        # Other
        elif isinstance(expr, Lit):
            return f"{expr.val()}", expr.type
        elif isinstance(expr, Var):
            if expr.name() in vars_to_replace:
                return helper(vars_to_replace[expr.name()], vars_to_replace)
            return expr.name(), expr.type
        return str(expr)

    return helper(ps_fn_decl.body())[0]
