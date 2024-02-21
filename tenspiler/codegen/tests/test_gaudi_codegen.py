from metalift.ir import Int, Ite, List, Matrix, call, fn_decl_recursive
from tenspiler.codegen.gaudi_codegen import gaudi_codegen
from tenspiler.codegen.utils import DataType
from tenspiler.tenspiler_common import (
    MATRIX_SELECTION_TWO_ARGS,
    SELECT_TWO_ARGS,
    dissolve_select_two_args_fn_obj_arg,
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
        fn_decl = func(codegen_func)

        # Post-processing code
        codegen_result = codegen_func(fn_decl, [], d_type=DataType.INT)
        print(codegen_result)

    return wrapper


@codegen
def normal_blend_8(codegen_func):
    fn_decl = fn_decl_recursive(
        "normal_blend_8_ps",
        List[Int],
        call(
            "vec_elemwise_add",
            List[Int],
            call("vec_scalar_mul", List[Int], opacity, active_vec),
            call("vec_scalar_mul", List[Int], 255 - opacity, base_vec),
        ),
        base_vec,
        active_vec,
        opacity,
    )
    return fn_decl, [], DataType.INT


@codegen
def normal_blend_f(codegen_func):
    fn_decl = fn_decl_recursive(
        "normal_blend_f_ps",
        List[Int],
        call(
            "vec_elemwise_add",
            List[Int],
            call("vec_scalar_mul", List[Int], opacity, active_vec),
            call("vec_scalar_mul", List[Int], 1 - opacity, base_vec),
        ),
        base_vec,
        active_vec,
        opacity,
    )
    return fn_decl, [], DataType.FLOAT


@codegen
def dissolve_blend_8(codegen_func):
    rand_cons = Int("rand_cons")
    rand_val = (rand_cons % 100) // 100
    select_two_args_fn_decl = fn_decl_recursive(
        SELECT_TWO_ARGS,
        Int,
        Ite(opacity - rand_val >= 0, int_y, int_x),
        int_x,
        int_y,
        opacity,
        rand_cons,
    )

    fn_decl = fn_decl_recursive(
        "dissolve_blend_8_ps",
        Matrix[Int],
        call(
            MATRIX_SELECTION_TWO_ARGS,
            Matrix[Int],
            base_matrix,
            active_matrix,
            opacity,
            rand_cons,
            dissolve_select_two_args_fn_obj_arg,
        ),
    )
    return fn_decl, [fn_decl, select_two_args_fn_decl], DataType.INT


@codegen
def darken_blend_8(codegen_func):
    select_two_args_fn_decl = fn_decl_recursive(
        SELECT_TWO_ARGS,
        Int,
        Ite(int_x > int_y, int_y, int_x),
        int_x,
        int_y,
    )

    fn_decl = fn_decl_recursive(
        "darken_blend_8_ps",
        Matrix[Int],
        call(
            MATRIX_SELECTION_TWO_ARGS,
            Matrix[Int],
            base_matrix,
            active_matrix,
            select_two_args_fn_obj_arg,
        ),
    )
    return fn_decl, [fn_decl, select_two_args_fn_decl], DataType.INT


@codegen
def multiply_blend_8(codegen_func):
    fn_decl = fn_decl_recursive(
        "multiply_blend_8_ps",
        Matrix[Int],
        call(
            "matrix_scalar_div",
            Matrix[Int],
            Int(255),
            call("matrix_elemwise_mul", Matrix[Int], base_matrix, active_matrix),
        ),
        base_matrix,
        active_matrix,
    )
    return fn_decl, [], DataType.INT


@codegen
def linear_burn_8(codegen_func):
    fn_decl = fn_decl_recursive(
        "linear_burn_8_ps",
        Matrix[Int],
        call(
            "matrix_scalar_sub",
            Int(255),
            call("matrix_elemwise_add", base_matrix, active_matrix),
            Matrix[Int],
            base_matrix,
            active_matrix,
            select_two_args_fn_obj_arg,
        ),
    )
    return fn_decl, [fn_decl, select_two_args_fn_decl], DataType.INT


normal_blend_8(gaudi_codegen)
