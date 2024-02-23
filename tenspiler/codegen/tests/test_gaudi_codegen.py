from metalift.ir import Int, List, Matrix, fn_decl_recursive, ite
from tenspiler.codegen.gaudi_codegen import gaudi_codegen
from tenspiler.codegen.mlx_codegen import mlx_codegen
from tenspiler.codegen.utils import DataType
from tenspiler.tenspiler_common import (
    DISSOLVE_MATRIX_SELECTION_TWO_ARGS,
    DISSOLVE_SELECT_TWO_ARGS,
    MATRIX_SELECTION_TWO_ARGS,
    SELECT_TWO_ARGS,
    call_dissolve_matrix_selection_two_args,
    call_matrix_selection_two_args,
    dissolve_matrix_selection_two_args_fn_decl,
    dissolve_select_two_args_fn_obj_arg,
    matrix_selection_two_args_fn_decl,
    select_two_args_fn_obj_arg,
)

base_matrix = Matrix(Int, "base")
active_matrix = Matrix(Int, "active")
base_vec = List(Int, "base")
active_vec = List(Int, "active")
opacity = Int("opacity")
int_x = Int("int_x")
int_y = Int("int_y")


def codegen(func):
    def wrapper(codegen_func):
        # Execute the original function
        ps_fn_decl, all_fn_decls, d_type = func(codegen_func)

        # Post-processing code
        codegen_result = codegen_func(ps_fn_decl, all_fn_decls, d_type=d_type)
        print(codegen_result)

    return wrapper


@codegen
def normal_blend_8(codegen_func):
    fn_decl = fn_decl_recursive(
        "normal_blend_8_ps",
        List[Int],
        List.add(List.mul(opacity, active_vec), List.mul(255 - opacity, base_vec)),
        base_vec,
        active_vec,
        opacity,
    )
    all_fn_decls = {"normal_blend_8_ps": fn_decl}
    return fn_decl, all_fn_decls, DataType.INT


@codegen
def normal_blend_f(codegen_func):
    fn_decl = fn_decl_recursive(
        "normal_blend_f_ps",
        List[Int],
        List.add(List.mul(opacity, active_vec), List.mul(1 - opacity, base_vec)),
        base_vec,
        active_vec,
        opacity,
    )
    all_fn_decls = {"normal_blend_f_ps": fn_decl}
    return fn_decl, all_fn_decls, DataType.FLOAT


@codegen
def dissolve_blend_8(codegen_func):
    rand_cons = Int("rand_cons")
    rand_val = (rand_cons % 100) // 100
    select_two_args_fn_decl = fn_decl_recursive(
        DISSOLVE_SELECT_TWO_ARGS,
        Int,
        ite(opacity - rand_val >= 0, int_y, int_x),
        int_x,
        int_y,
        opacity,
        rand_cons,
    )

    fn_decl = fn_decl_recursive(
        "dissolve_blend_8_ps",
        Matrix[Int],
        call_dissolve_matrix_selection_two_args(
            base_matrix,
            active_matrix,
            opacity,
            rand_cons,
            dissolve_select_two_args_fn_obj_arg,
        ),
    )
    all_fn_decls = {
        DISSOLVE_SELECT_TWO_ARGS: select_two_args_fn_decl,
        DISSOLVE_MATRIX_SELECTION_TWO_ARGS: dissolve_matrix_selection_two_args_fn_decl,
        "dissolve_blend_8_ps": fn_decl,
    }
    return fn_decl, all_fn_decls, DataType.INT


@codegen
def darken_blend_8(codegen_func):
    select_two_args_fn_decl = fn_decl_recursive(
        SELECT_TWO_ARGS,
        Int,
        ite(int_x > int_y, int_y, int_x),
        int_x,
        int_y,
    )

    fn_decl = fn_decl_recursive(
        "darken_blend_8_ps",
        Matrix[Int],
        call_matrix_selection_two_args(
            base_matrix,
            active_matrix,
            select_two_args_fn_obj_arg,
        ),
    )
    all_fn_decls = {
        SELECT_TWO_ARGS: select_two_args_fn_decl,
        MATRIX_SELECTION_TWO_ARGS: matrix_selection_two_args_fn_decl,
        "darken_blend_8_ps": fn_decl,
    }
    return fn_decl, all_fn_decls, DataType.INT


@codegen
def multiply_blend_8(codegen_func):
    fn_decl = fn_decl_recursive(
        "multiply_blend_8_ps",
        Matrix[Int],
        Matrix.div(Matrix.mul(base_matrix, active_matrix), 255),
        base_matrix,
        active_matrix,
    )
    return fn_decl, [fn_decl], DataType.INT


@codegen
def linear_burn_8(codegen_func):
    fn_decl = fn_decl_recursive(
        "linear_burn_8_ps",
        Matrix[Int],
        Matrix.sub(Matrix.add(base_matrix, active_matrix), 255),
        base_matrix,
        active_matrix,
    )
    all_fn_decls = {"linear_burn_8_ps": fn_decl}
    return fn_decl, all_fn_decls, DataType.INT


@codegen
def color_burn_8(codegen_func):
    select_two_args_fn_decl = fn_decl_recursive(
        SELECT_TWO_ARGS,
        Int,
        ite(int_y == 0, Int(255), 255 - (255 - int_x) // int_y),
        int_x,
        int_y,
    )

    fn_decl = fn_decl_recursive(
        "color_burn_8_ps",
        Matrix[Int],
        call_matrix_selection_two_args(
            base_matrix,
            active_matrix,
            select_two_args_fn_obj_arg,
        ),
    )
    all_fn_decls = {
        SELECT_TWO_ARGS: select_two_args_fn_decl,
        MATRIX_SELECTION_TWO_ARGS: matrix_selection_two_args_fn_decl,
        "color_burn_8_ps": fn_decl,
    }
    return fn_decl, all_fn_decls, DataType.INT


@codegen
def lighten_blend_8(codegen_func):
    select_two_args_fn_decl = fn_decl_recursive(
        SELECT_TWO_ARGS,
        Int,
        ite(int_x > int_y, int_x, int_y),
        int_x,
        int_y,
    )

    fn_decl = fn_decl_recursive(
        "lighten_blend_8_ps",
        Matrix[Int],
        call_matrix_selection_two_args(
            base_matrix,
            active_matrix,
            select_two_args_fn_obj_arg,
        ),
    )
    all_fn_decls = {
        SELECT_TWO_ARGS: select_two_args_fn_decl,
        MATRIX_SELECTION_TWO_ARGS: matrix_selection_two_args_fn_decl,
        "lighten_blend_8_ps": fn_decl,
    }
    return fn_decl, all_fn_decls, DataType.INT


@codegen
def screen_blend_8(codegen_func):
    fn_decl = fn_decl_recursive(
        "screen_blend_8_ps",
        Matrix[Int],
        Matrix.sub(
            Matrix.add(base_matrix, active_matrix),
            Matrix.div(Matrix.mul(base_matrix, active_matrix), 255),
        ),
        base_matrix,
        active_matrix,
    )
    return fn_decl, [fn_decl], DataType.INT


@codegen
def linear_dodge_8(codegen_func):
    fn_decl = fn_decl_recursive(
        "linear_dodge_8_ps",
        Matrix[Int],
        Matrix.add(base_matrix, active_matrix),
        base_matrix,
        active_matrix,
    )
    return fn_decl, [fn_decl], DataType.INT


@codegen
def color_dodge_8(codegen_func):
    select_two_args_fn_decl = fn_decl_recursive(
        SELECT_TWO_ARGS,
        Int,
        ite(int_y == 255, Int(255), int_x // (255 - int_y)),
        int_x,
        int_y,
    )

    fn_decl = fn_decl_recursive(
        "color_dodge_8_ps",
        Matrix[Int],
        call_matrix_selection_two_args(
            base_matrix,
            active_matrix,
            select_two_args_fn_obj_arg,
        ),
    )
    all_fn_decls = {
        SELECT_TWO_ARGS: select_two_args_fn_decl,
        MATRIX_SELECTION_TWO_ARGS: matrix_selection_two_args_fn_decl,
        "color_dodge_8_ps": fn_decl,
    }
    return fn_decl, all_fn_decls, DataType.INT


@codegen
def overlay_blend_8(codegen_func):
    select_two_args_fn_decl = fn_decl_recursive(
        SELECT_TWO_ARGS,
        Int,
        ite(
            int_x >= 128,
            2 * int_x + int_x - 2 * int_x * int_x // 255 - 255,
            2 * int_x * int_y // 255,
        ),
        int_x,
        int_y,
    )

    fn_decl = fn_decl_recursive(
        "overlay_blend_8_ps",
        Matrix[Int],
        call_matrix_selection_two_args(
            base_matrix,
            active_matrix,
            select_two_args_fn_obj_arg,
        ),
    )
    all_fn_decls = {
        SELECT_TWO_ARGS: select_two_args_fn_decl,
        MATRIX_SELECTION_TWO_ARGS: matrix_selection_two_args_fn_decl,
        "overlay_blend_8_ps": fn_decl,
    }
    return fn_decl, all_fn_decls, DataType.INT


codegen_funcs = [mlx_codegen, gaudi_codegen]
for codegen_func in codegen_funcs[:1]:
    normal_blend_8(codegen_func)
    normal_blend_f(codegen_func)
    dissolve_blend_8(codegen_func)
    darken_blend_8(codegen_func)
    multiply_blend_8(codegen_func)
    linear_burn_8(codegen_func)
    color_burn_8(codegen_func)
    lighten_blend_8(codegen_func)
    screen_blend_8(codegen_func)
    linear_dodge_8(codegen_func)
    color_dodge_8(codegen_func)
    overlay_blend_8(codegen_func)
