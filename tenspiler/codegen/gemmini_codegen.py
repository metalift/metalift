import textwrap
from typing import Any, Dict, List, Tuple, Union

from metalift.ir import (
    Add,
    And,
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
    Ite,
    Le,
)
from metalift.ir import List as mlList
from metalift.ir import Lit, Lt, Matrix, Mod, Mul, Not, ObjectT, Or, Sub, Var
from tenspiler.codegen.utils import DataType
from tenspiler.tenspiler_common import (
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

# Indentation is 4 spaces
INDENTATION = " " * 4

translations = {
    VEC_ELEMWISE_ADD: lambda processed_args, curr_var, var_dimensions: f"tiled_resadd_auto({var_dimensions[curr_var][0]}, {var_dimensions[curr_var][1]}, 1, 1, 1, {processed_args[0]}[0], {processed_args[1]}[0], {curr_var}[0], false, WS); \n",
    MATRIX_ELEMWISE_ADD: lambda processed_args, curr_var, var_dimensions: f"tiled_resadd_auto({var_dimensions[curr_var][0]}, {var_dimensions[curr_var][1]}, 1, 1, 1, {processed_args[0]}[0], {processed_args[1]}[0], {curr_var}[0], false, WS); \n",
    VEC_SCALAR_ADD: lambda processed_args, curr_var, var_dimensions, is_floor=False: f"for (int i = 0; i < {var_dimensions[curr_var][0]}; i++) {{ \n \t {curr_var}[i][0] = {processed_args[0]}[i][0] + {processed_args[1]}; \n }} \n",
    MATRIX_SCALAR_ADD: lambda processed_args, curr_var, var_dimensions, is_floor=False: f"for (int i = 0; i < {var_dimensions[curr_var][0]}; i++) {{ \n \t for (int j = 0; j < {var_dimensions[curr_var][1]}; j++) {{ \n \t \t {curr_var}[i][j] = {processed_args[0]}[i][j] + {processed_args[1]}; \n \t }} \n }} \n",
    VEC_ELEMWISE_SUB: lambda processed_args, curr_var, var_dimensions: f"tiled_resadd_auto({var_dimensions[curr_var][0]}, {var_dimensions[curr_var][1]}, 1, -1, 1, {processed_args[0]}[0], {processed_args[1]}[0], {curr_var}[0], false, WS); \n",
    MATRIX_ELEMWISE_SUB: lambda processed_args, curr_var, var_dimensions: f"tiled_resadd_auto({var_dimensions[curr_var][0]}, {var_dimensions[curr_var][1]}, 1, -1, 1, {processed_args[0]}[0], {processed_args[1]}[0], {curr_var}[0], false, WS); \n",
    SCALAR_VEC_SUB: lambda processed_args, curr_var, var_dimensions, is_floor=False: f"for (int i = 0; i < {var_dimensions[curr_var][0]}; i++) {{ \n \t {curr_var}[i][0] = {processed_args[0]} - {processed_args[1]}[i][0]; \n }} \n",
    SCALAR_MATRIX_SUB: lambda processed_args, curr_var, var_dimensions, is_floor=False: f"for (int i = 0; i < {var_dimensions[curr_var][0]}; i++) {{ \n \t for (int j = 0; j < {var_dimensions[curr_var][1]}; j++) {{ \n \t \t {curr_var}[i][j] = {processed_args[0]} - {processed_args[1]}[i][j]; \n \t }} \n }} \n",
    VEC_SCALAR_SUB: lambda processed_args, curr_var, var_dimensions, is_floor=False: f"for (int i = 0; i < {var_dimensions[curr_var][0]}; i++) {{ \n \t {curr_var}[i][0] = {processed_args[1]}[i][0] - {processed_args[0]}; \n }} \n",
    MATRIX_SCALAR_SUB: lambda processed_args, curr_var, var_dimensions, is_floor=False: f"for (int i = 0; i < {var_dimensions[curr_var][0]}; i++) {{ \n \t for (int j = 0; j < {var_dimensions[curr_var][1]}; j++) {{ \n \t \t {curr_var}[i][j] = {processed_args[1]}[i][j] - {processed_args[0]}; \n \t }} \n }} \n",
    VEC_ELEMWISE_MUL: lambda processed_args, curr_var, var_dimensions: f"for (int i = 0; i < {var_dimensions[curr_var][0]}; i++) {{ \n \t {curr_var}[i][0] = {processed_args[0]}[i][0] * {processed_args[1]}[i][0]; \n }} \n",
    MATRIX_ELEMWISE_MUL: lambda processed_args, curr_var, var_dimensions: f"for (int i = 0; i < {var_dimensions[curr_var][0]}; i++) {{ \n \t for (int j = 0; j < {var_dimensions[curr_var][1]}; j++) {{ \n \t \t {curr_var}[i][j] = {processed_args[0]}[i][j] * {processed_args[1]}[i][j]; \n \t }} \n }} \n",
    VEC_SCALAR_MUL: lambda processed_args: f"GEMMINI_ACC_SCALE({processed_args[1]}, {processed_args[0]}); \n",
    MATRIX_SCALAR_MUL: lambda processed_args: f"GEMMINI_ACC_SCALE({processed_args[1]}, {processed_args[0]}); \n",
    VEC_ELEMWISE_DIV: lambda processed_args, curr_var, var_dimensions, is_floor=False: f"for (int i = 0; i < {var_dimensions[curr_var][0]}; i++) {{ \n \t {curr_var}[i][0] = {processed_args[0]}[i][0] / (float){processed_args[1]}[i][0]; \n }} \n",
    MATRIX_ELEMWISE_DIV: lambda processed_args, curr_var, var_dimensions, is_floor=False: f"for (int i = 0; i < {var_dimensions[curr_var][0]}; i++) {{ \n \t for (int j = 0; j < {var_dimensions[curr_var][1]}; j++) {{ \n \t \t {curr_var}[i][j] = {processed_args[0]}[i][j] / (float){processed_args[1]}[i][j]; \n \t }} \n }} \n",
    SCALAR_VEC_DIV: lambda processed_args, curr_var, var_dimensions, is_floor=False: f"for (int i = 0; i < {var_dimensions[curr_var][0]}; i++) {{ \n \t {curr_var}[i][0] = {processed_args[0]} / (float) {processed_args[1]}[i][0]; \n }} \n",
    SCALAR_MATRIX_DIV: lambda processed_args, curr_var, var_dimensions, is_floor=False: f"for (int i = 0; i < {var_dimensions[curr_var][0]}; i++) {{ \n \t for (int j = 0; j < {var_dimensions[curr_var][1]}; j++) {{ \n \t \t {curr_var}[i][j] = {processed_args[0]} / (float){processed_args[1]}[i][j]; \n \t }} \n }} \n",
    VEC_SCALAR_DIV: lambda processed_args, is_floor=False: f"GEMMINI_ACC_SCALE({processed_args[1]}, 1 / (float){processed_args[0]}); \n",
    MATRIX_SCALAR_DIV: lambda processed_args, is_floor=False: f"GEMMINI_ACC_SCALE({processed_args[1]}, 1 / (float){processed_args[0]}); \n",
    "matrix_vec_mul": lambda processed_args, curr_var: f"tiled_matmul_auto(LEN, LEN, 1, (elem_t*) {processed_args[0]}, (elem_t*) {processed_args[1]}, NULL, {curr_var}, 1, LEN, LEN, LEN, 1, 1, 1, 0, 1, 0, false, false, false, false, 0, 0, WS); \n",
    "reduce_sum": lambda processed_args, curr_var, var_dimensions: f"tiled_global_average({processed_args[0]}[0], (elem_t*) {curr_var}, 1, 1, {var_dimensions[curr_var][0]}, 1); \n",
    "list_take": lambda processed_args, curr_var: f"for (int i = 0; i < {processed_args[1]}; i++) {{ \n \t {curr_var}[i][0] = {processed_args[0]}[i][0]; \n }} \n",
    "matrix_take": lambda processed_args, curr_var, var_dimensions: f"for (int i = 0; i < {processed_args[1]}; i++) {{ \n \t for (int j = 0; j < {var_dimensions[curr_var][1]}; j++) {{ \n \t \t {curr_var}[i][j] = {processed_args[0]}[i][j]; \n \t }} \n }} \n",
    "matrix_col_slice": lambda processed_args, curr_var, var_dimensions: f"for (int i = 0; i < {var_dimensions[curr_var][0]}; i++) {{ \n \t for (int j = {processed_args[1]}; j < {processed_args[2]}; j++) {{ \n \t \t {curr_var}[i][j] = {processed_args[0]}[i][j]; \n \t }} \n }} \n",
    "matrix_row_slice": lambda processed_args, curr_var, var_dimensions: f"for (int i = {processed_args[1]}; i < {processed_args[2]}; i++) {{ \n \t for (int j = 0; j < {var_dimensions[curr_var][1]}; j++) {{ \n \t \t {curr_var}[i][j] = {processed_args[0]}[i][j]; \n \t }} \n }} \n",
    "list_length": lambda processed_args, curr_var, var_dimensions: f"{var_dimensions[processed_args[0]][0]}",
    "matrix_length": lambda processed_args, curr_var, var_dimensions: f"{var_dimensions[processed_args[0]][0] * var_dimensions[processed_args[0]][0]}",
    "matrix_transpose": lambda processed_args, curr_var, var_dimensions: f"for (int i = 0; i < {var_dimensions[curr_var][0]}; i++) {{ \n \t for (int j = 0; j < {var_dimensions[curr_var][0]}; j++) {{ \n \t \t {curr_var}[i][j] = {processed_args[0]}[j][i]; \n \t }} \n }} \n",
    Add: lambda processed_args: f"({processed_args[0]}) + ({processed_args[1]})",
    Sub: lambda processed_args: f"({processed_args[0]}) - ({processed_args[1]})",
    Mul: lambda processed_args: f"({processed_args[0]}) * ({processed_args[1]})",
    Div: lambda processed_args: f"({processed_args[0]}) / ({processed_args[1]})",
    Mod: lambda processed_args: f"({processed_args[0]}) % ({processed_args[1]})",
}

glue_var_count = 0


def gemmini_type_helper(var_type, var_name, var_dimensions):
    if var_type == Matrix[Int] or var_type == mlList[Int]:
        var_dimensions[var_name] = ["LEN", "LEN"]
        return f"elem_t {var_name}[LEN][LEN]"
    elif var_type == Int:
        var_dimensions[var_name] = ["1", "1"]
        return f"elem_t {var_name}"
    elif var_type == Bool:
        var_dimensions[var_name] = ["1", "1"]
        return f"bool {var_name}"
    else:
        raise Exception(f"unsupported input type {var_type}")


def c_type_helper(var_type, var_name, d_type):
    if var_type == Matrix[Int]:
        return f"{d_type} {var_name}[LEN][LEN]"
    elif var_type == mlList[Int]:
        return f"{d_type} {var_name}[LEN]"
    elif var_type == Int:
        return f"{d_type} {var_name}"
    elif var_type == Bool:
        return f"bool {var_name}"
    else:
        raise Exception(f"unsupported input type {var_type}")


def c_argument_convert_helper(
    var_type, var_name, d_type, conversions, converted_arguments
):
    global glue_var_count
    if var_type == mlList[Int]:
        glue_var_name = f"glued_{glue_var_count}"
        glue_var_count += 1
        conversions.append(f"static {d_type} {glue_var_name}[LEN][LEN];")
        conversions.append(
            f"""
        for (int i = 0; i < LEN; i++) {{
            {glue_var_name}[i][0] = {var_name}[i];
        }}
        """
        )
        converted_arguments.append(glue_var_name)
    else:
        converted_arguments.append(var_name)


def gemmini_codegen(
    ps_fn_decl: Union[FnDecl, FnDeclRecursive],
    all_synthesized_fns: Dict[str, Expr],
    d_type: DataType = DataType.FLOAT,
) -> str:
    temp_var_count: int = 0

    def helper(
        expr: Any,
        vars_to_replace: Dict[str, Expr] = {},
        curr_var: str = "",
        var_dimensions: Dict[str, List[str]] = {},
    ) -> Tuple[str, ObjectT]:
        nonlocal temp_var_count
        global translations
        if not isinstance(expr, Expr):
            return str(expr), None
        if isinstance(expr, Call):
            processed_args = []
            res = ""
            fn_name = expr.name()
            # special case optimization
            if fn_name == VEC_ELEMWISE_ADD or fn_name == MATRIX_ELEMWISE_ADD:
                args = expr.arguments()
                if (
                    isinstance(args[0], Call)
                    and isinstance(args[1], Call)
                    and args[0].name() == VEC_SCALAR_MUL
                    and args[1].name() == VEC_SCALAR_MUL
                ):
                    expr1_args = [
                        helper(arg, vars_to_replace, "", var_dimensions)[0]
                        for arg in args[0].arguments()
                    ]
                    expr2_args = [
                        helper(arg, vars_to_replace, "", var_dimensions)[0]
                        for arg in args[1].arguments()
                    ]
                    var_dimensions[curr_var] = [
                        var_dimensions[expr1_args[1]][0],
                        var_dimensions[expr1_args[1]][1],
                    ]
                    return (
                        f"tiled_resadd_auto({var_dimensions[curr_var][0]}, {var_dimensions[curr_var][1]}, {expr1_args[0]}, {expr2_args[0]}, 1, {expr1_args[1]}[0], {expr2_args[1]}[0], {curr_var}[0], false, WS); \n",
                        expr.type,
                    )

            for arg in expr.arguments():
                if isinstance(arg, Call) or isinstance(arg, Ite):
                    temp_var_name = f"temp{temp_var_count}"
                    temp_var_count += 1
                    # this assumes down stream call will actually add "var =" if needed. it will also add the dimentionality to var_dimensions if necessary
                    (var_expr, var_type, *rest) = helper(
                        arg, vars_to_replace, temp_var_name, var_dimensions
                    )

                    if var_type == Matrix[Int] or var_type == mlList[Int]:
                        var_def = f"static elem_t {temp_var_name}[LEN][LEN]; \n"
                    elif var_type == Int:
                        var_def = f"static elem_t {temp_var_name}; \n"
                        continue
                    elif var_type == Bool:
                        var_def = f"static bool {temp_var_name}; \n"
                        continue
                    else:
                        raise Exception(f"Cannot create variable of type {var_type}")
                    res += var_def
                    res += var_expr
                    processed_args.append(temp_var_name)
                else:
                    processed_args.append(
                        helper(arg, vars_to_replace, "", var_dimensions)[0]
                    )

            if fn_name == VEC_ELEMWISE_ADD or fn_name == MATRIX_ELEMWISE_ADD:
                var_dimensions[curr_var] = [
                    var_dimensions[processed_args[0]][0],
                    var_dimensions[processed_args[0]][1],
                ]
                return (
                    res
                    + translations[fn_name](processed_args, curr_var, var_dimensions),
                    expr.type,
                )
            elif fn_name == VEC_ELEMWISE_SUB or fn_name == MATRIX_ELEMWISE_SUB:
                var_dimensions[curr_var] = [
                    var_dimensions[processed_args[0]][0],
                    var_dimensions[processed_args[0]][1],
                ]
                return (
                    res
                    + translations[fn_name](processed_args, curr_var, var_dimensions),
                    expr.type,
                )
            elif fn_name == VEC_ELEMWISE_MUL or fn_name == MATRIX_ELEMWISE_MUL:
                var_dimensions[curr_var] = [
                    var_dimensions[processed_args[0]][0],
                    var_dimensions[processed_args[0]][1],
                ]
                return (
                    res
                    + translations[fn_name](processed_args, curr_var, var_dimensions),
                    expr.type,
                )
            elif fn_name == VEC_ELEMWISE_DIV or fn_name == MATRIX_ELEMWISE_DIV:
                var_dimensions[curr_var] = [
                    var_dimensions[processed_args[0]][0],
                    var_dimensions[processed_args[0]][1],
                ]
                return (
                    res
                    + translations[fn_name](processed_args, curr_var, var_dimensions),
                    expr.type,
                )
            elif (
                fn_name == VEC_SCALAR_ADD
                or fn_name == MATRIX_SCALAR_ADD
                or fn_name == VEC_SCALAR_SUB
                or fn_name == MATRIX_SCALAR_SUB
            ):
                var_dimensions[curr_var] = [
                    var_dimensions[processed_args[1]][0],
                    var_dimensions[processed_args[1]][1],
                ]
                return (
                    res
                    + translations[fn_name](processed_args, curr_var, var_dimensions),
                    expr.type,
                )
            elif (
                fn_name == VEC_SCALAR_MUL
                or fn_name == MATRIX_SCALAR_MUL
                or fn_name == VEC_SCALAR_DIV
                or fn_name == MATRIX_SCALAR_DIV
            ):
                var_dimensions[curr_var] = [
                    var_dimensions[processed_args[1]][0],
                    var_dimensions[processed_args[1]][1],
                ]
                res = res + translations[fn_name](processed_args)
                # This is needed since scale doesn't involve assignment
                if processed_args[1] != curr_var:
                    res = (
                        res
                        + f"memcpy({processed_args[1]}, {curr_var}, sizeof(elem_t) * LEN * LEN); \n"
                    )
                return res, expr.type
            elif (
                fn_name == SCALAR_VEC_SUB
                or fn_name == SCALAR_MATRIX_SUB
                or fn_name == SCALAR_VEC_DIV
                or fn_name == SCALAR_MATRIX_DIV
            ):
                var_dimensions[curr_var] = [
                    var_dimensions[processed_args[1]][0],
                    var_dimensions[processed_args[1]][1],
                ]
                return (
                    res
                    + translations[fn_name](processed_args, curr_var, var_dimensions),
                    expr.type,
                )

            elif fn_name == "matrix_vec_mul":
                var_dimensions[curr_var] = [
                    var_dimensions[processed_args[0]][0],
                    var_dimensions[processed_args[1]][1],
                ]
                res += translations[fn_name](processed_args, curr_var)
                return res, expr.type
            elif fn_name == "reduce_sum":
                res += translations[fn_name](processed_args, curr_var, var_dimensions)
                if curr_var != "out":
                    res += f"{curr_var} = {curr_var} * LEN * LEN; \n"
                else:
                    res += f"*{curr_var} = *{curr_var} * LEN * LEN; \n"
                return res, expr.type

            elif fn_name == "list_take":
                var_dimensions[curr_var] = [processed_args[1], processed_args[1]]
                return res + translations[fn_name](processed_args, curr_var), expr.type
            elif fn_name == "matrix_take":
                var_dimensions[curr_var] = var_dimensions[processed_args[0]]
                return (
                    res
                    + translations[fn_name](processed_args, curr_var, var_dimensions),
                    expr.type,
                )
            elif fn_name == "matrix_col_slice":
                var_dimensions[curr_var] = var_dimensions[processed_args[0]]
                return (
                    res
                    + translations[fn_name](processed_args, curr_var, var_dimensions),
                    expr.type,
                )
            elif fn_name == "matrix_row_slice":
                var_dimensions[curr_var] = var_dimensions[processed_args[0]]
                return (
                    res
                    + translations[fn_name](processed_args, curr_var, var_dimensions),
                    expr.type,
                )
            elif fn_name == "list_length" or fn_name == "matrix_length":
                return (
                    res
                    + translations[fn_name](processed_args, curr_var, var_dimensions),
                    expr.type,
                )
            elif fn_name == "matrix_transpose":
                var_dimensions[curr_var] = var_dimensions[processed_args[0]]
                return (
                    res
                    + translations[fn_name](processed_args, curr_var, var_dimensions),
                    expr.type,
                )
            elif fn_name in all_synthesized_fns.keys():
                return helper(
                    all_synthesized_fns[fn_name].body(),
                    vars_to_replace,
                    curr_var,
                    var_dimensions,
                )

            raise Exception(f"Unknown function name: {fn_name}")

        # Ite expression. Some condition are constants
        if isinstance(expr, Ite):
            cond = helper(expr.c())[0]

            if cond == "True":
                return helper(expr.e1(), vars_to_replace, curr_var, var_dimensions)
            elif cond == "False":
                return helper(expr.e2(), vars_to_replace, curr_var, var_dimensions)
            else:
                return (
                    f"""
if ({cond}) {{
    {helper(expr.e1(), vars_to_replace, curr_var, var_dimensions)[0]}}}
else {{
    {helper(expr.e2(), vars_to_replace, curr_var, var_dimensions)[0]}
}}
""",
                    expr.e1().type,
                )

        # Arithmetic operations
        processed_args = [
            helper(arg, vars_to_replace, "", var_dimensions) for arg in expr.args
        ]
        processed_args_types = [a[1] for a in processed_args]
        processed_args = [a[0] for a in processed_args]
        if any(isinstance(expr, cls) for cls in [Add, Sub, Mul, Div, Mod]):
            is_arg_type_int = all([a_type is Int for a_type in processed_args_types])
            ret_type = (
                Int
                if is_arg_type_int
                else [
                    a_type
                    for a_type in processed_args_types
                    if a_type is not Int and a_type is not None
                ][0]
            )
            if ret_type != Int:
                raise Exception(f"Arithmatic of non-integer type")
            if isinstance(expr, Div) and d_type != DataType.FLOAT:
                return translations["float_div"](processed_args), ret_type
            return translations[type(expr)](processed_args), ret_type
        # Relational operations
        elif any(isinstance(expr, cls) for cls in [Gt, Ge, Eq, Lt, Le]):
            is_arg_type_int = all([a_type is Int for a_type in processed_args_types])
            ret_type = Bool if is_arg_type_int else mlList[Bool]
            if ret_type != Bool:
                raise Exception(f"Relational that doesn't return Bool")
            return translations[type(expr)](processed_args, is_arg_type_int), ret_type
        elif any(isinstance(expr, cls) for cls in [And, Or, Not]):
            is_arg_type_prim = all(
                [a_type is Int or a_type is Bool for a_type in processed_args_types]
            )
            ret_type = Bool if is_arg_type_prim else mlList[Bool]
            if ret_type != Bool:
                raise Exception(f"Logical that doesn't return Bool")
            return translations[type(expr)](processed_args, is_arg_type_prim), ret_type

        # Other
        elif isinstance(expr, Lit):
            return f"{expr.val()}", expr.type
        elif isinstance(expr, Var):
            if expr.name() in vars_to_replace:
                return helper(
                    vars_to_replace[expr.name()], vars_to_replace, "", var_dimensions
                )
            return expr.name(), expr.type
        return str(expr)

    ###############################
    # Begins actual code generation
    ###############################
    import_stmt = """
// include statements
#include \"include/gemmini_params.h\"
#include \"include/gemmini.h\"
//# define LEN 200, change as needed
//note elem_t is defined in gemmini_params.h and is defaulted to int8_t
"""
    print(import_stmt)

    result_var = "out"

    fn_name = f"{ps_fn_decl.name()[:-3]}"
    arguments = [arg.name() for arg in ps_fn_decl.arguments()]
    argument_types = [arg.type for arg in ps_fn_decl.arguments()]

    var_str = []
    var_dimensions = {}
    for i in range(len(arguments)):
        var_str.append(
            gemmini_type_helper(argument_types[i], arguments[i], var_dimensions)
        )

    if ps_fn_decl.returnT() == Matrix[Int] or ps_fn_decl.returnT() == mlList[Int]:
        var_dimensions[result_var] = ["LEN", "LEN"]
        var_str.append(f"elem_t {result_var}[LEN][LEN]")
    elif ps_fn_decl.returnT() == Int or ps_fn_decl.returnT() == Bool:
        var_dimensions[result_var] = ["1", "1"]
        var_str.append(f"elem_t* {result_var}")
    else:
        raise Exception(f"Unsupported return type {ps_fn_decl.returnT()}")

    arguments_str = ", ".join(var_str)

    kernel_name = f"{fn_name}_gemmini"
    print("####### kernel code ########")
    kernel_fn = f"""
    void {kernel_name}({arguments_str}){{
{textwrap.indent(helper(ps_fn_decl.body(), {}, result_var, var_dimensions)[0], INDENTATION * 2)}
    }}
    """
    kernel_fn = textwrap.dedent(kernel_fn)
    print(kernel_fn)

    print("####### glued code ########")
    glued_name = f"{fn_name}_gemmini_glued "

    # C glue function parameters
    lib_dtype = "uint8_t"

    if d_type == DataType.FLOAT:
        lib_dtype = "float"

    if d_type == DataType.INT32:
        lib_dtype = "int32_t"

    var_str_c = []
    for i in range(len(arguments)):
        var_str_c.append(c_type_helper(argument_types[i], arguments[i], lib_dtype))
    arguments_str_c = ", ".join(var_str_c)

    # C glue code preprocessing
    conversions = []
    converted_arguments = []
    for i in range(len(arguments)):
        c_argument_convert_helper(
            argument_types[i], arguments[i], "elem_t", conversions, converted_arguments
        )

    # C glue code. out variable initialization
    if ps_fn_decl.returnT() == Int or ps_fn_decl.returnT() == Bool:
        converted_arguments.append(f"&{result_var}")
    else:
        converted_arguments.append(result_var)

    if ps_fn_decl.returnT() == Matrix[Int] or ps_fn_decl.returnT() == mlList[Int]:
        conversions.append(f"static {lib_dtype} {result_var} [LEN][LEN];")
    elif ps_fn_decl.returnT() == Int:
        conversions.append(f"elem_t {result_var};")
    elif ps_fn_decl.returnT() == Bool:
        conversions.append(f"bool {result_var};")

    # C glue code. out variable post processing if necessary
    rv = result_var
    postprocess = []
    if ps_fn_decl.returnT() == mlList[Int]:
        old_rv = rv
        rv = "out_postprocess"
        postprocess.append(f"static {lib_dtype} {rv} [LEN]; \n")
        postprocess.append(
            f"""
        for (int i = 0; i < LEN; i++) {{
            {rv}[i] = {old_rv}[i][0];
        }}
        """
        )

    # C glue code. function definition return value
    ret_type_c = ""
    if ps_fn_decl.returnT() in [Matrix[Int], mlList[Int]]:
        ret_type_c = f"{lib_dtype}*"
    elif ps_fn_decl.returnT() == Int:
        ret_type_c = f"{lib_dtype}"
    elif ps_fn_decl.returnT() == Bool:
        ret_type_c = "bool"
    elif ps_fn_decl.returnT() == None:
        ret_type_c = "void"
    else:
        raise Exception(f"Unsupported return type {ps_fn_decl.returnT()}")

    arg_processing = f"\n{INDENTATION * 2}".join(conversions)
    rv_postprocessing = f"\n{INDENTATION * 2}".join(postprocess)
    glued_fn = f"""
    {ret_type_c} {glued_name}({arguments_str_c}){{
        {arg_processing}
        {kernel_name}({", ".join(converted_arguments)});
        {rv_postprocessing}
        return {rv};
    }}
    """
    glued_fn = textwrap.dedent(glued_fn)
    print(glued_fn)

    return import_stmt + kernel_fn + glued_fn
