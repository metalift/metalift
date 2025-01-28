from metalift.ir import Int, List, Matrix, fn_decl_recursive, ite
from tenspiler.codegen.gaudi_codegen import gaudi_codegen
from tenspiler.codegen.utils import DataType
from tenspiler.tenspiler_common import (
    DISSOLVE_MATRIX_SELECTION_TWO_ARGS,
    DISSOLVE_SELECT_TWO_ARGS,
    MAP_INT_TO_INT,
    MATRIX_WHERE,
    SELECT_TWO_ARGS,
    call_dissolve_matrix_selection_two_args,
    call_integer_exp,
    call_integer_sqrt,
    call_map_int_to_int,
    call_matrix_selection_two_args,
    call_matrix_vec_mul,
    call_reduce_max,
    call_reduce_sum,
    call_vec_map,
    dissolve_matrix_selection_two_args_fn_decl,
    dissolve_select_two_args_fn_obj_arg,
    map_int_to_int_fn_obj,
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


def normal_blend_8():
    fn_decl = fn_decl_recursive(
        "normal_blend_8_ps",
        List[Int],
        List.add(List.mul(opacity, active_vec), List.mul(255 - opacity, base_vec)),
        base_vec,
        active_vec,
        opacity,
    )
    all_fn_decls = {"normal_blend_8_ps": fn_decl}
    return fn_decl, all_fn_decls, DataType.UINT_8


def normal_blend_f():
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


def dissolve_blend_8():
    rand_cons = Int("rand_cons")
    rand_val = (rand_cons % 100 + 1) // 100
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
        base_matrix,
        active_matrix,
        opacity,
        rand_cons,
    )
    all_fn_decls = {
        DISSOLVE_SELECT_TWO_ARGS: select_two_args_fn_decl,
        DISSOLVE_MATRIX_SELECTION_TWO_ARGS: dissolve_matrix_selection_two_args_fn_decl,
        "dissolve_blend_8_ps": fn_decl,
    }
    return fn_decl, all_fn_decls, DataType.UINT_8


def darken_blend_8():
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
        base_matrix,
        active_matrix,
    )
    all_fn_decls = {
        SELECT_TWO_ARGS: select_two_args_fn_decl,
        MATRIX_WHERE: matrix_selection_two_args_fn_decl,
        "darken_blend_8_ps": fn_decl,
    }
    return fn_decl, all_fn_decls, DataType.UINT_8


def multiply_blend_8():
    fn_decl = fn_decl_recursive(
        "multiply_blend_8_ps",
        Matrix[Int],
        Matrix.div(Matrix.mul(base_matrix, active_matrix), 255),
        base_matrix,
        active_matrix,
    )
    all_fn_decls = {"multiply_blend_8_ps": fn_decl}
    return fn_decl, all_fn_decls, DataType.UINT_8


def linear_burn_8():
    fn_decl = fn_decl_recursive(
        "linear_burn_8_ps",
        Matrix[Int],
        Matrix.sub(Matrix.add(base_matrix, active_matrix), 255),
        base_matrix,
        active_matrix,
    )
    all_fn_decls = {"linear_burn_8_ps": fn_decl}
    return fn_decl, all_fn_decls, DataType.UINT_8


def color_burn_8():
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
        base_matrix,
        active_matrix,
    )
    all_fn_decls = {
        SELECT_TWO_ARGS: select_two_args_fn_decl,
        MATRIX_WHERE: matrix_selection_two_args_fn_decl,
        "color_burn_8_ps": fn_decl,
    }
    return fn_decl, all_fn_decls, DataType.UINT_8


def lighten_blend_8():
    select_two_args_fn_decl = fn_decl_recursive(
        SELECT_TWO_ARGS,
        Int,
        ite(int_x < int_y, int_y, int_x),
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
        base_matrix,
        active_matrix,
    )
    all_fn_decls = {
        SELECT_TWO_ARGS: select_two_args_fn_decl,
        MATRIX_WHERE: matrix_selection_two_args_fn_decl,
        "lighten_blend_8_ps": fn_decl,
    }
    return fn_decl, all_fn_decls, DataType.UINT_8


def screen_blend_8():
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
    all_fn_decls = {"screen_blend_8_ps": fn_decl}
    return fn_decl, all_fn_decls, DataType.UINT_8


def linear_dodge_8():
    fn_decl = fn_decl_recursive(
        "linear_dodge_8_ps",
        Matrix[Int],
        Matrix.add(base_matrix, active_matrix),
        base_matrix,
        active_matrix,
    )
    all_fn_decls = {"linear_dodge_8_ps": fn_decl}
    return fn_decl, all_fn_decls, DataType.UINT_8


def color_dodge_8():
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
        base_matrix,
        active_matrix,
    )
    all_fn_decls = {
        SELECT_TWO_ARGS: select_two_args_fn_decl,
        MATRIX_WHERE: matrix_selection_two_args_fn_decl,
        "color_dodge_8_ps": fn_decl,
    }
    return fn_decl, all_fn_decls, DataType.UINT_8


def overlay_blend_8():
    select_two_args_fn_decl = fn_decl_recursive(
        SELECT_TWO_ARGS,
        Int,
        ite(
            int_x >= 128,
            2 * int_x + int_x - 2 * int_x * int_x // 255 - 255,
            2 * int_x * int_x // 255,
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
        base_matrix,
        active_matrix,
    )
    all_fn_decls = {
        SELECT_TWO_ARGS: select_two_args_fn_decl,
        MATRIX_WHERE: matrix_selection_two_args_fn_decl,
        "overlay_blend_8_ps": fn_decl,
    }
    return fn_decl, all_fn_decls, DataType.UINT_8


# Llama benchmarks


def softmax_part1():
    input = List(Int, "input")
    max_pos = Int("max_pos")
    fn_decl = fn_decl_recursive(
        "softmax_part1_ps", Int, call_reduce_max(input[:max_pos]), input, max_pos
    )
    all_fn_decls = {"softmax_part1_ps": fn_decl}
    return fn_decl, all_fn_decls, DataType.FLOAT


def softmax_part2():
    input = List(Int, "input")
    max_pos = Int("max_pos")
    max_val = Int("max_val")
    fn_decl = fn_decl_recursive(
        "softmax_part2_ps",
        List[Int],
        call_vec_map(List.sub(input[:max_pos], max_val), map_int_to_int_fn_obj),
        input,
        max_pos,
        max_val,
    )
    int_x = Int("int_x")
    map_int_to_int_fn_decl = fn_decl_recursive(
        MAP_INT_TO_INT, Int, call_integer_exp(int_x), int_x
    )
    all_fn_decls = {MAP_INT_TO_INT: map_int_to_int_fn_decl, "softmax_part2_ps": fn_decl}
    return fn_decl, all_fn_decls, DataType.FLOAT


def softmax_part3():
    output = List(Int, "output")
    max_pos = Int("max_pos")
    fn_decl = fn_decl_recursive(
        "softmax_part3_ps", Int, call_reduce_sum(output[:max_pos]), output, max_pos
    )
    all_fn_decls = {"softmax_part3_ps": fn_decl}
    return fn_decl, all_fn_decls, DataType.FLOAT


def softmax_part4():
    unnormalized_output = List(Int, "unnormalized_output")
    max_pos = Int("max_pos")
    sum = Int("sum")
    fn_decl = fn_decl_recursive(
        "softmax_part4_ps",
        List[Int],
        List.div(unnormalized_output[:max_pos], sum),
        unnormalized_output,
        max_pos,
        sum,
    )
    all_fn_decls = {"softmax_part4_ps": fn_decl}
    return fn_decl, all_fn_decls, DataType.FLOAT


def rmsnorm_part1():
    input = List(Int, "input")
    weight = List(Int, "weight")
    fn_decl = fn_decl_recursive(
        "rmsnorm_part1_ps", Int, call_reduce_sum(List.mul(input, input)), input, weight
    )
    all_fn_decls = {"rmsnorm_part1_ps": fn_decl}
    return fn_decl, all_fn_decls, DataType.FLOAT


def rmsnorm_part2():
    input = List(Int, "input")
    weight = List(Int, "weight")
    ss = Int("ss")
    cons = 1 // call_integer_sqrt(ss // input.len() + 1)
    fn_decl = fn_decl_recursive(
        "rmsnorm_part2_ps",
        Int,
        List.mul(cons, List.mul(input, weight)),
        input,
        weight,
        ss,
    )
    all_fn_decls = {"rmsnorm_part2_ps": fn_decl}
    return fn_decl, all_fn_decls, DataType.FLOAT


def matmul():
    weight = Matrix(Int, "weight")
    input = List(Int, "input")
    fn_decl = fn_decl_recursive(
        "matmul_ps",
        List[Int],
        call_matrix_vec_mul(weight, input),
        weight,
        input,
    )
    all_fn_decls = {"matmul_ps": fn_decl}
    return fn_decl, all_fn_decls, DataType.FLOAT


def transformer_part1():
    token_position = Int("token_position")
    head = Int("head")
    head_size = Int("head_size")
    key_cache_layer = Matrix(Int, "key_cache_layer")
    q = List(Int, "q")
    computed_vec = call_matrix_vec_mul(
        key_cache_layer[:token_position].col_slice_with_length(
            head * head_size, head_size
        ),
        q.slice_with_length(head * head_size, head_size),
    )
    fn_decl = fn_decl_recursive(
        "transformer_part1_ps",
        List[Int],
        List.div(computed_vec, call_map_int_to_int(head_size * 1)),
        token_position,
        head,
        head_size,
        key_cache_layer,
        q,
    )
    map_int_to_int_fn_decl = fn_decl_recursive(
        MAP_INT_TO_INT, Int, call_integer_sqrt(int_x), int_x
    )
    all_fn_decls = {
        MAP_INT_TO_INT: map_int_to_int_fn_decl,
        "transformer_part1_ps": fn_decl,
    }
    return fn_decl, all_fn_decls, DataType.FLOAT


def transformer_part2():
    token_position = Int("token_position")
    head = Int("head")
    head_size = Int("head_size")
    key_cache_layer = Matrix(Int, "key_cache_layer")
    attention = List(Int, "attention")
    computed_vec = call_matrix_vec_mul(
        key_cache_layer[: token_position + 1]
        .col_slice_with_length(head * head_size, head_size)
        .transpose(),
        attention[: token_position + 1],
    )
    fn_decl = fn_decl_recursive(
        "transformer_part2_ps",
        List[Int],
        computed_vec,
        token_position,
        head,
        head_size,
        key_cache_layer,
        attention,
    )
    all_fn_decls = {"transformer_part2_ps": fn_decl}
    return fn_decl, all_fn_decls, DataType.FLOAT


def transformer_part3():
    input = List(Int, "input")
    hidden_dim = Int("hidden_dim")

    fn_decl = fn_decl_recursive(
        "transformer_part3_ps",
        List[Int],
        List.mul(
            input[:hidden_dim],
            List.div(
                1,
                List.add(
                    1,
                    call_vec_map(
                        List.sub(0, input[:hidden_dim]), map_int_to_int_fn_obj
                    ),
                ),
            ),
        ),
        input,
        hidden_dim,
    )
    map_int_to_int_fn_decl = fn_decl_recursive(
        MAP_INT_TO_INT, Int, call_integer_exp(int_x), int_x
    )
    all_fn_decls = {
        MAP_INT_TO_INT: map_int_to_int_fn_decl,
        "transformer_part3_ps": fn_decl,
    }
    return fn_decl, all_fn_decls, DataType.FLOAT


def transformer_part4():
    input1 = List(Int, "input1")
    input2 = List(Int, "input2")
    hidden_dim = Int("hidden_dim")
    fn_decl = fn_decl_recursive(
        "transformer_part4_ps",
        List[Int],
        List.mul(input1[:hidden_dim], input2[:hidden_dim]),
        input1,
        input2,
        hidden_dim,
    )
    all_fn_decls = {"transformer_part4_ps": fn_decl}
    return fn_decl, all_fn_decls, DataType.FLOAT


def test_type():
    input = List(Int, "input")
    hidden_dim = Int("hidden_dim")
    fn_decl = fn_decl_recursive(
        "test_type_ps",
        List[Int],
        List.mul(input[:hidden_dim], input[:hidden_dim]),
        input,
        hidden_dim,
    )
    all_fn_decls = {"test_type_ps": fn_decl}
    return fn_decl, all_fn_decls, DataType.FLOAT


def dot():
    a = List(Int, "a")
    b = List(Int, "b")
    n = Int("n")
    fn_decl = fn_decl_recursive(
        "dot_ps", Int, call_reduce_sum(List.mul(a[:n], b[:n])), a, b, n
    )
    all_fn_decls = {"dot_ps": fn_decl}
    return fn_decl, all_fn_decls, DataType.INT32


# codegen_funcs = [mlx_codegen, numpy_codegen, pytorch_codegen, tensorflow_codegen]
codegen_funcs = [gaudi_codegen]

for codegen_func in codegen_funcs:
    print(*dot())
    codegen_func(*dot())
    exit(0)
    codegen_func(*test_type())

    codegen_func(*dissolve_blend_8())
    codegen_func(*darken_blend_8())
    codegen_func(*color_burn_8())
    codegen_func(*lighten_blend_8())
    codegen_func(*color_dodge_8())
    codegen_func(*overlay_blend_8())
    codegen_func(*multiply_blend_8())
    codegen_func(*linear_burn_8())
    codegen_func(*screen_blend_8())
    codegen_func(*linear_dodge_8())
    codegen_func(*normal_blend_f())
    codegen_func(*normal_blend_8())
    exit(0)

    codegen_func(*matmul())
    codegen_func(*transformer_part1())
    codegen_func(*transformer_part2())
    codegen_func(*transformer_part3())
    codegen_func(*transformer_part4())
    codegen_func(*rmsnorm_part1())
    codegen_func(*rmsnorm_part2())
    codegen_func(*softmax_part1())
    codegen_func(*softmax_part2())
    codegen_func(*softmax_part3())
    codegen_func(*softmax_part4())
