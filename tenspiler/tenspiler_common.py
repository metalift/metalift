from typing import Any, Callable, Dict, List, Optional, Tuple, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, Fn, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import (
    Matrix,
    Object,
    Synth,
    Tensor3D,
    call,
    call_value,
    choose,
    fn_decl,
    fn_decl_recursive,
    get_list_element_type,
    is_list_type,
    is_matrix_type,
    is_primitive_type,
    is_tensor3d_type,
    ite,
    synth,
)
from metalift.vc_util import and_objects, or_objects

# Reduce functions
REDUCESUM = "reduce_sum"
REDUCEMUL = "reduce_mul"
REDUCEMAX = "reduce_max"

# Elemwise functions
VEC_ELEMWISE_ADD = "vec_elemwise_add"
MATRIX_ELEMWISE_ADD = "matrix_elemwise_add"
TENSOR3D_ELEMWISE_ADD = "tensor3d_elemwise_add"
VEC_ELEMWISE_SUB = "vec_elemwise_sub"
MATRIX_ELEMWISE_SUB = "matrix_elemwise_sub"
TENSOR3D_ELEMWISE_SUB = "tensor3d_elemwise_sub"
VEC_ELEMWISE_MUL = "vec_elemwise_mul"
MATRIX_ELEMWISE_MUL = "matrix_elemwise_mul"
TENSOR3D_ELEMWISE_MUL = "tensor3d_elemwise_mul"
VEC_ELEMWISE_DIV = "vec_elemwise_div"
MATRIX_ELEMWISE_DIV = "matrix_elemwise_div"
TENSOR3D_ELEMWISE_DIV = "tensor3d_elemwise_div"

# Scalar functions
VEC_SCALAR_ADD = "vec_scalar_add"
MATRIX_SCALAR_ADD = "matrix_scalar_add"
VEC_SCALAR_MUL = "vec_scalar_mul"
MATRIX_SCALAR_MUL = "matrix_scalar_mul"
# scalar on the right hand side
VEC_SCALAR_DIV = "vec_scalar_div"
MATRIX_SCALAR_DIV = "matrix_scalar_div"
VEC_SCALAR_SUB = "vec_scalar_sub"
MATRIX_SCALAR_SUB = "matrix_scalar_sub"
# scalar on the left hand side
SCALAR_VEC_DIV = "scalar_vec_div"
SCALAR_MATRIX_DIV = "scalar_matrix_div"
SCALAR_VEC_SUB = "scalar_vec_sub"
SCALAR_MATRIX_SUB = "scalar_matrix_sub"

# Selection functions
SELECT_TWO_ARGS = "select_two_args"
DISSOLVE_SELECT_TWO_ARGS = "dissolve_select_two_args"
SELECT_TWO_ARGS_ARG = "select_two_args_arg"
DISSOLVE_SELECT_TWO_ARGS_ARG = "dissolve_select_two_args_arg"
SELECTION_TWO_ARGS = "selection_two_args"
DISSOLVE_SELECTION_TWO_ARGS = "dissolve_selection_two_args"
MATRIX_SELECTION_TWO_ARGS = "matrix_selection_two_args"
DISSOLVE_MATRIX_SELECTION_TWO_ARGS = "dissolve_matrix_selection_two_args"

# Uninterpreted functions
MAP_INT_TO_INT = "map_int_to_int"
# Integer functions
INTEGER_EXP = "integer_exp"
INTEGER_SQRT = "integer_sqrt"

# Operations that involve uninterpreted functions
VEC_MAP = "vec_map"

# Other helper functions
MATRIX_VEC_MUL = "matrix_vec_mul"
ITE_INT = "ite_int"

TensorT = Union[mlList[Int], Matrix[Int], Tensor3D[Int]]


def call_elemwise_add(left: TensorT, right: TensorT) -> TensorT:
    if is_tensor3d_type(left.type):
        return call_tensor_3d_elemwise_add(left, right)
    elif is_matrix_type(left.type):
        return call_matrix_elemwise_add(left, right)
    else:
        return call_vec_elemwise_add(left, right)


def call_elemwise_sub(left: TensorT, right: TensorT) -> TensorT:
    if is_matrix_type(left.type):
        return call_matrix_elemwise_sub(left, right)
    else:
        return call_vec_elemwise_sub(left, right)


def call_elemwise_mul(left: TensorT, right: TensorT) -> TensorT:
    if is_tensor3d_type(left.type):
        return call_tensor_3d_elemwise_mul(left, right)
    elif is_matrix_type(left.type):
        return call_matrix_elemwise_mul(left, right)
    else:
        return call_vec_elemwise_mul(left, right)


def call_elemwise_div(left: TensorT, right: TensorT) -> TensorT:
    if is_matrix_type(left.type):
        return call_matrix_elemwise_div(left, right)
    else:
        return call_vec_elemwise_div(left, right)


def call_scalar_add(scalar: Int, matrix_or_vec: TensorT) -> TensorT:
    if is_matrix_type(matrix_or_vec.type):
        return call_matrix_scalar_add(scalar, matrix_or_vec)
    else:
        return call_vec_scalar_add(scalar, matrix_or_vec)


def call_scalar_sub(scalar: Int, matrix_or_vec: TensorT) -> TensorT:
    if is_matrix_type(matrix_or_vec.type):
        return call_matrix_scalar_sub(scalar, matrix_or_vec)
    else:
        return call_vec_scalar_sub(scalar, matrix_or_vec)


def call_scalar_mul(scalar: Int, matrix_or_vec: TensorT) -> TensorT:
    if is_matrix_type(matrix_or_vec.type):
        return call_matrix_scalar_mul(scalar, matrix_or_vec)
    else:
        return call_vec_scalar_mul(scalar, matrix_or_vec)


def call_scalar_div(scalar: Int, matrix_or_vec: TensorT) -> TensorT:
    if is_matrix_type(matrix_or_vec.type):
        return call_matrix_scalar_div(scalar, matrix_or_vec)
    else:
        return call_vec_scalar_div(scalar, matrix_or_vec)


def call_scalar_rsub(scalar: Int, matrix_or_vec: TensorT) -> TensorT:
    if is_matrix_type(matrix_or_vec.type):
        return call_scalar_matrix_sub(scalar, matrix_or_vec)
    else:
        return call_scalar_vec_sub(scalar, matrix_or_vec)


def call_scalar_rdiv(scalar: Int, matrix_or_vec: TensorT) -> TensorT:
    if is_matrix_type(matrix_or_vec.type):
        return call_scalar_matrix_div(scalar, matrix_or_vec)
    else:
        return call_scalar_vec_div(scalar, matrix_or_vec)


def call_vec_elemwise_add(left: mlList[Int], right: mlList[Int]) -> mlList[Int]:
    return call(VEC_ELEMWISE_ADD, mlList[Int], left, right)


def call_vec_elemwise_sub(left: mlList[Int], right: mlList[Int]) -> mlList[Int]:
    return call(VEC_ELEMWISE_SUB, mlList[Int], left, right)


def call_vec_elemwise_mul(left: mlList[Int], right: mlList[Int]) -> mlList[Int]:
    return call(VEC_ELEMWISE_MUL, mlList[Int], left, right)


def call_vec_elemwise_div(left: mlList[Int], right: mlList[Int]) -> mlList[Int]:
    return call(VEC_ELEMWISE_DIV, mlList[Int], left, right)


def call_vec_scalar_add(scalar: Int, vec: mlList[Int]) -> mlList[Int]:
    return call(VEC_SCALAR_ADD, mlList[Int], scalar, vec)


def call_vec_scalar_sub(scalar: Int, vec: mlList[Int]) -> mlList[Int]:
    return call(VEC_SCALAR_SUB, mlList[Int], scalar, vec)


def call_vec_scalar_mul(scalar: Int, vec: mlList[Int]) -> mlList[Int]:
    return call(VEC_SCALAR_MUL, mlList[Int], scalar, vec)


def call_vec_scalar_div(scalar: Int, vec: mlList[Int]) -> mlList[Int]:
    return call(VEC_SCALAR_DIV, mlList[Int], scalar, vec)


def call_scalar_vec_sub(scalar: Int, vec: mlList[Int]) -> mlList[Int]:
    return call(SCALAR_VEC_SUB, mlList[Int], scalar, vec)


def call_scalar_vec_div(scalar: Int, vec: mlList[Int]) -> mlList[Int]:
    return call(SCALAR_VEC_DIV, mlList[Int], scalar, vec)


def call_matrix_elemwise_add(left: Matrix[Int], right: Matrix[Int]) -> Matrix[Int]:
    return call(MATRIX_ELEMWISE_ADD, Matrix[Int], left, right)


def call_matrix_elemwise_sub(left: Matrix[Int], right: Matrix[Int]) -> Matrix[Int]:
    return call(MATRIX_ELEMWISE_SUB, Matrix[Int], left, right)


def call_matrix_elemwise_mul(left: Matrix[Int], right: Matrix[Int]) -> Matrix[Int]:
    return call(MATRIX_ELEMWISE_MUL, Matrix[Int], left, right)


def call_matrix_elemwise_div(left: Matrix[Int], right: Matrix[Int]) -> Matrix[Int]:
    return call(MATRIX_ELEMWISE_DIV, Matrix[Int], left, right)


def call_matrix_scalar_add(scalar: Int, matrix: Matrix[Int]) -> Matrix[Int]:
    return call(MATRIX_SCALAR_ADD, Matrix[Int], scalar, matrix)


def call_matrix_scalar_mul(scalar: Int, matrix: Matrix[Int]) -> Matrix[Int]:
    return call(MATRIX_SCALAR_MUL, Matrix[Int], scalar, matrix)


def call_matrix_scalar_div(scalar: Int, matrix: Matrix[Int]) -> Matrix[Int]:
    return call(MATRIX_SCALAR_DIV, Matrix[Int], scalar, matrix)


def call_matrix_scalar_sub(scalar: Int, matrix: Matrix[Int]) -> Matrix[Int]:
    return call(MATRIX_SCALAR_SUB, Matrix[Int], scalar, matrix)


def call_scalar_matrix_sub(scalar: Int, matrix: Matrix[Int]) -> Matrix[Int]:
    return call(SCALAR_MATRIX_SUB, Matrix[Int], scalar, matrix)


def call_scalar_matrix_div(scalar: Int, matrix: Matrix[Int]) -> Matrix[Int]:
    return call(SCALAR_MATRIX_DIV, Matrix[Int], scalar, matrix)


def call_tensor_3d_elemwise_add(
    left: Tensor3D[Int], right: Tensor3D[Int]
) -> Tensor3D[Int]:
    return call(TENSOR3D_ELEMWISE_ADD, Tensor3D[Int], left, right)


def call_tensor_3d_elemwise_mul(
    left: Tensor3D[Int], right: Tensor3D[Int]
) -> Tensor3D[Int]:
    return call(TENSOR3D_ELEMWISE_MUL, Tensor3D[Int], left, right)


def call_reduce_sum(lst) -> Int:
    return call(REDUCESUM, Int, lst)


def call_reduce_mul(lst) -> Int:
    return call(REDUCEMUL, Int, lst)


def call_reduce_max(lst) -> Int:
    return call(REDUCEMAX, Int, lst)


def call_selection_two_args(
    left: mlList[Int], right: mlList[Int], select_fn: Fn[tuple[Int, Int, Int]]
) -> mlList[Int]:
    return call(SELECTION_TWO_ARGS, mlList[Int], left, right, select_fn)


def call_dissolve_selection_two_args(
    left: mlList[Int],
    right: mlList[Int],
    opacity: Int,
    rand_cons: Int,
    select_fn: Fn[tuple[Int, Int, Int]],
) -> mlList[Int]:
    return call(
        DISSOLVE_SELECTION_TWO_ARGS,
        mlList[Int],
        left,
        right,
        opacity,
        rand_cons,
        select_fn,
    )


def call_matrix_selection_two_args(
    left: Matrix[Int], right: Matrix[Int], select_fn: Fn[tuple[Int, Int, Int]]
) -> Matrix[Int]:
    return call(MATRIX_SELECTION_TWO_ARGS, Matrix[Int], left, right, select_fn)


def call_matrix_selection(left: Matrix[Int], right: Matrix[Int]) -> Matrix[Int]:
    return call(MATRIX_SELECTION_TWO_ARGS, Matrix[Int], left, right)


def call_selection(left: mlList[Int], right: mlList[Int]) -> mlList[Int]:
    return call(SELECTION_TWO_ARGS, mlList[Int], left, right)


def call_dissolve_matrix_selection(
    left: Matrix[Int], right: Matrix[Int], opacity: Int, rand_cons: Int
) -> Matrix[Int]:
    return call(
        DISSOLVE_MATRIX_SELECTION_TWO_ARGS, Matrix[Int], left, right, opacity, rand_cons
    )


def call_dissolve_selection(
    left: mlList[Int], right: mlList[Int], opacity: Int, rand_cons: Int
) -> mlList[Int]:
    return call(
        DISSOLVE_SELECTION_TWO_ARGS, mlList[Int], left, right, opacity, rand_cons
    )


def call_dissolve_matrix_selection_two_args(
    left: Matrix[Int],
    right: Matrix[Int],
    opacity: Int,
    rand_cons: Int,
    select_fn: Fn[tuple[Int, Int, Int]],
) -> Matrix[Int]:
    return call(
        DISSOLVE_MATRIX_SELECTION_TWO_ARGS,
        Matrix[Int],
        left,
        right,
        opacity,
        rand_cons,
        select_fn,
    )


def call_integer_exp(x: Int) -> Int:
    return call(INTEGER_EXP, Int, x)


def call_integer_sqrt(x: Int) -> Int:
    return call(INTEGER_SQRT, Int, x)


def call_map_int_to_int(x: Int) -> Int:
    return call(MAP_INT_TO_INT, Int, x)


def call_vec_map(x: mlList[Int], map_fn: Fn[tuple[Int, Int]]) -> mlList[Int]:
    return call(VEC_MAP, mlList[Int], x, map_fn)


def call_matrix_vec_mul(matrix: Matrix[Int], vec: mlList[Int]) -> mlList[Int]:
    return call(MATRIX_VEC_MUL, mlList[Int], matrix, vec)


vec_vec_to_vec = lambda left, right: choose(
    call_vec_elemwise_add(left, right),
    call_vec_elemwise_sub(left, right),
    call_vec_elemwise_mul(left, right),
    call_vec_elemwise_div(left, right),
)
scalar_vec_to_vec = lambda num, vec: choose(
    call_vec_scalar_add(num, vec),
    call_vec_scalar_sub(num, vec),
    call_vec_scalar_mul(num, vec),
    call_vec_scalar_div(num, vec),
    call_scalar_vec_sub(num, vec),
    call_scalar_vec_div(num, vec),
)
vec_to_int = lambda vec: choose(
    call_reduce_sum(vec), call_reduce_mul(vec), call_reduce_max(vec)
)
vec_to_vec = lambda vec: choose(call_vec_map(vec, map_int_to_int_fn_obj))
matrix_vec_to_vec = lambda matrix, vec: choose(call_matrix_vec_mul(matrix, vec))

# Define some common objects
a = Int("a")
x = mlList(Int, "x")
y = mlList(Int, "y")
matrix_x = Matrix(Int, "matrix_x")
matrix_y = Matrix(Int, "matrix_y")
tensor3d_x = Tensor3D(Int, "tensor3d_x")
tensor3d_y = Tensor3D(Int, "tensor3d_y")
int_x = Int("int_x")
int_y = Int("int_y")
opacity = Int("opacity")
rand_cons = Int("rand_cons")
cond = Bool("cond")


def reduce_sum_body(lst: List[Int]) -> Int:
    vec_size = lst.len()
    cur = lst[0]
    lst_rest = lst[1:]
    recursed = call_reduce_sum(lst_rest)
    general_answer = cur + recursed
    return ite(vec_size < 1, Int(0), general_answer)


reduce_sum = fn_decl_recursive(REDUCESUM, Int, reduce_sum_body(x), x)


def reduce_mul_body(lst: mlList[Int]) -> Int:
    vec_size = lst.len()
    cur = lst[0]
    lst_rest = lst[1:]
    recursed = call_reduce_mul(lst_rest)
    general_answer = cur * recursed
    return ite(vec_size < 1, Int(1), general_answer)


reduce_mul = fn_decl_recursive(REDUCEMUL, Int, reduce_mul_body(x), x)


def reduce_max_body(lst: mlList[Int]) -> Int:
    vec_size = lst.len()
    cur = lst[0]
    lst_rest = lst[1:]
    recursed = call_reduce_max(lst_rest)
    general_answer = ite(cur > recursed, cur, recursed)
    # TODO(sahil)
    return ite(vec_size < 1, 0 - Int(32), ite(vec_size == 1, lst[0], general_answer))


reduce_max = fn_decl_recursive(REDUCEMAX, Int, reduce_max_body(x), x)


def matrix_vec_mul_body(matrix: Matrix[Int], vec: mlList[Int]) -> mlList[Int]:
    invalid_cond = or_objects(
        matrix.len() < 1, matrix[0].len() < 1, matrix[0].len() != vec.len()
    )
    cur = call_reduce_sum(call_vec_elemwise_mul(matrix[0], vec))
    recursed = call_matrix_vec_mul(matrix[1:], vec)
    return ite(invalid_cond, mlList.empty(Int), recursed.prepend(cur))


matrix_vec_mul = fn_decl_recursive(
    MATRIX_VEC_MUL, mlList[Int], matrix_vec_mul_body(matrix_x, x), matrix_x, x
)

ite_int = fn_decl(ITE_INT, Int, ite(cond, int_x, int_y), cond, int_x, int_y)


# Helper functions for selections
def mul8x8_div32_body(int_x: Int, int_y: Int) -> Int:
    return (int_x * int_y) // 32


def screen8x8_body(int_x: Int, int_y: Int) -> Int:
    return int_x + int_y - mul8x8_div32_body(int_x, int_y)


# Helper functions for compute functions
def vec_mul8x8_div32_body(x: mlList[Int], y: mlList[Int]) -> mlList[Int]:
    return call_vec_scalar_div(
        Int(32),
        call_vec_elemwise_mul(x, y),
    )


def matrix_mul8x8_div32_body(
    nested_x: Matrix[Int], nested_y: Matrix[Int]
) -> Matrix[Int]:
    return call_matrix_scalar_div(Int(32), call_matrix_elemwise_mul(nested_x, nested_y))


def vec_screen8x8_body(x: mlList[Int], y: mlList[Int]) -> mlList[Int]:
    return call_vec_elemwise_sub(
        call_vec_elemwise_add(x, y), vec_mul8x8_div32_body(x, y)
    )


def matrix_screen8x8_body(nested_x: Matrix[Int], nested_y: Matrix[Int]) -> Matrix[Int]:
    return call_matrix_elemwise_sub(
        call_matrix_elemwise_add(nested_x, nested_y),
        matrix_mul8x8_div32_body(nested_x, nested_y),
    )


def vec_linear_burn_body(x: mlList[Int], y: mlList[Int]) -> mlList[Int]:
    return call_vec_scalar_sub(
        Int(32),
        call_vec_elemwise_add(x, y),
    )


def matrix_linear_burn_body(
    nested_x: Matrix[Int], nested_y: Matrix[Int]
) -> Matrix[Int]:
    return call_matrix_scalar_sub(Int(32), call_matrix_elemwise_add(nested_x, nested_y))


# Helper functions for compute benchmarks using the holing approach
def multiply_blend_8_hole_body(matrix_or_vec: TensorT) -> TensorT:
    cons = choose(Int(32))
    return call_scalar_div(cons, call_elemwise_mul(matrix_or_vec, matrix_or_vec))


def linear_burn_8_hole_body(matrix_or_vec: TensorT) -> TensorT:
    cons = choose(Int(32))
    return call_scalar_sub(cons, call_elemwise_add(matrix_or_vec, matrix_or_vec))


def screen_blend_8_hole_body(matrix_or_vec: TensorT) -> TensorT:
    cons = choose(Int(32))
    return call_elemwise_sub(
        call_elemwise_add(matrix_or_vec, matrix_or_vec),
        call_scalar_div(cons, call_elemwise_mul(matrix_or_vec, matrix_or_vec)),
    )


def linear_dodge_8_hole_body(matrix_or_vec: TensorT) -> TensorT:
    return call_elemwise_add(matrix_or_vec, matrix_or_vec)


# Helper functions for select benchmarks using the holing approach
def dissolve_blend_8_hole_body(int_var: Int) -> Int:
    cons = choose(Int(0), Int(1), Int(100))
    int_var = choose(int_var, ((int_var % cons) + cons) // cons)
    return ite((int_var - int_var) >= cons, int_var, int_var)


def darken_blend_8_hole_body(int_var: Int) -> Int:
    return ite(int_var > int_var, int_var, int_var)


def color_burn_8_hole_body(int_var: Int) -> Int:
    cons = choose(Int(0), Int(32))
    return ite(int_var == cons, cons, cons - (cons - int_var) // int_var)


def lighten_blend_8_hole_body(int_var: Int) -> Int:
    return ite(int_var < int_var, int_var, int_var)


def color_dodge_8_hole_body(int_var: Int) -> Int:
    cons = choose(Int(32))
    return ite(int_var == cons, cons, int_var // (cons - int_var))


def overlay_blend_8_hole_body(int_var: Int) -> Int:
    cons = choose(Int(2), Int(16), Int(32))
    return ite(
        int_var >= cons,
        cons * int_var + int_var - cons * int_var * int_var // cons - cons,
        cons * int_var * int_var // cons,
    )


# Selection criteria
def select_darken_blend_body(int_x: Int, int_y: Int) -> Int:
    return ite(int_x > int_y, int_y, int_x)


def select_color_burn_body(int_x: Int, int_y: Int) -> Int:
    return ite(int_y == 0, Int(32), 32 - (32 - int_x) // int_y)


def select_lighten_blend_body(int_x: Int, int_y: Int) -> Int:
    return ite(int_x < int_y, int_y, int_x)


def select_color_dodge_body(int_x: Int, int_y: Int) -> Int:
    return ite(int_y == 32, Int(32), int_x // (32 - int_y))


def select_overlay_blend_body(int_x: Int, int_y: Int) -> Int:
    return ite(
        int_x >= 16,
        screen8x8_body(2 * int_x, int_x) - 32,
        mul8x8_div32_body(2 * int_x, int_x),
    )


select_two_args_fn_obj_arg = Fn((Int, Int, Int), SELECT_TWO_ARGS_ARG)
select_two_args_fn_obj = Fn((Int, Int, Int), SELECT_TWO_ARGS)
select_two_args_fn_decl = fn_decl(SELECT_TWO_ARGS, Int, None, int_x, int_y)

dissolve_select_two_args_fn_obj_arg = Fn(
    (Int, Int, Int, Int, Int), DISSOLVE_SELECT_TWO_ARGS_ARG
)
dissolve_select_two_args_fn_obj = Fn(
    (Int, Int, Int, Int, Int), DISSOLVE_SELECT_TWO_ARGS
)
dissolve_select_two_args_fn_decl = fn_decl(
    DISSOLVE_SELECT_TWO_ARGS, Int, None, int_x, int_y, opacity, rand_cons
)

map_int_to_int_fn_obj = Fn((Int, Int), MAP_INT_TO_INT)
map_int_to_int = fn_decl(MAP_INT_TO_INT, Int, None, int_x)


def matrix_selection_two_args_body(
    left: Matrix[Int], right: Matrix[Int], select_fn: Fn[tuple[Int, Int, Int]]
) -> Matrix[Int]:
    cur = call_selection_two_args(left[0], right[0], select_fn)
    recursed = call_matrix_selection_two_args(left[1:], right[1:], select_fn)
    general_answer = recursed.prepend(cur)
    return ite(
        or_objects(left.len() < 1, left.len() != right.len()),
        Matrix.empty(Int),
        general_answer,
    )


matrix_selection_two_args_fn_decl = fn_decl_recursive(
    MATRIX_SELECTION_TWO_ARGS,
    Matrix[Int],
    matrix_selection_two_args_body(matrix_x, matrix_y, select_two_args_fn_obj_arg),
    matrix_x,
    matrix_y,
    select_two_args_fn_obj_arg,
)


def dissolve_matrix_selection_two_args_body(
    left: Matrix[Int],
    right: Matrix[Int],
    opacity: Int,
    rand_cons: Int,
    dissolve_select_fn: Fn[tuple[Int, Int, Int, Int]],
) -> Matrix[Int]:
    cur = call_dissolve_selection_two_args(
        left[0], right[0], opacity, rand_cons, dissolve_select_fn
    )
    recursed = call_dissolve_matrix_selection_two_args(
        left[1:], right[1:], opacity, rand_cons, dissolve_select_fn
    )
    general_answer = recursed.prepend(cur)
    return ite(
        or_objects(left.len() < 1, left.len() != right.len()),
        Matrix.empty(Int),
        general_answer,
    )


dissolve_matrix_selection_two_args_fn_decl = fn_decl_recursive(
    DISSOLVE_MATRIX_SELECTION_TWO_ARGS,
    Matrix[Int],
    dissolve_matrix_selection_two_args_body(
        matrix_x, matrix_y, opacity, rand_cons, dissolve_select_two_args_fn_obj_arg
    ),
    matrix_x,
    matrix_y,
    opacity,
    rand_cons,
    dissolve_select_two_args_fn_obj_arg,
)


def selection_two_args_body(
    left: mlList[Int], right: mlList[Int], select_fn: Fn[tuple[Int, Int, Int]]
) -> mlList[Int]:
    cur = call_value(select_fn, left[0], right[0])
    recursed = call_selection_two_args(left[1:], right[1:], select_fn)
    general_answer = recursed.prepend(cur)
    return ite(
        or_objects(left.len() < 1, left.len() != right.len()),
        mlList.empty(Int),
        general_answer,
    )


selection_two_args_fn_decl = fn_decl_recursive(
    SELECTION_TWO_ARGS,
    mlList[Int],
    selection_two_args_body(x, y, select_two_args_fn_obj_arg),
    x,
    y,
    select_two_args_fn_obj_arg,
)


def dissolve_selection_two_args_body(
    left: mlList[Int],
    right: mlList[Int],
    opacity: Int,
    rand_cons: Int,
    dissolve_select_fn: Fn[tuple[Int, Int, Int, Int, Int]],
) -> mlList[Int]:
    cur = call_value(dissolve_select_fn, left[0], right[0], opacity, rand_cons)
    recursed = call_dissolve_selection_two_args(
        left[1:], right[1:], opacity, rand_cons, dissolve_select_fn
    )
    general_answer = recursed.prepend(cur)
    return ite(
        or_objects(left.len() < 1, left.len() != right.len()),
        mlList.empty(Int),
        general_answer,
    )


dissolve_selection_two_args_fn_decl = fn_decl_recursive(
    DISSOLVE_SELECTION_TWO_ARGS,
    mlList[Int],
    dissolve_selection_two_args_body(
        x, y, opacity, rand_cons, dissolve_select_two_args_fn_obj_arg
    ),
    x,
    y,
    opacity,
    rand_cons,
    dissolve_select_two_args_fn_obj_arg,
)


def selection_two_args_ps_grammar_fn(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    ret_val = writes[0]
    base, active = reads
    base_or_active = choose(base, active)
    return ret_val == call_matrix_selection_two_args(
        base_or_active, base_or_active, select_two_args_fn_obj
    )


def selection_two_args_inv0_grammar_fn(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    # outer loop grammar
    writes_by_name = {w.var_name(): w for w in writes}
    out = writes_by_name["agg.result"]
    col = writes_by_name["col"]
    row = writes_by_name["row"]
    base, active = reads
    index_lower_bound = choose(Int(0), Int(1))
    index_upper_bound = choose(base.len(), base[0].len(), active.len(), active[0].len())
    matrix = choose(
        base[:row],
        base[:col],
        active[:row],
        active[:col],
    )
    return and_objects(
        row >= index_lower_bound,
        row <= index_upper_bound,
        out == call_matrix_selection_two_args(matrix, matrix, select_two_args_fn_obj),
    )


def selection_two_args_inv1_grammar_fn(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    # inner loop grammar
    writes_by_name = {w.var_name(): w for w in writes}
    col = writes_by_name["col"]
    row_vec = writes_by_name["row_vec"]
    out, row = in_scope
    base, active = reads
    index_lower_bound = choose(Int(0), Int(1))
    index_upper_bound = choose(base.len(), base[0].len(), active.len(), active[0].len())
    vec = choose(
        base[row][:col],
        active[row][:col],
    )
    matrix = choose(base[:row], base[:col], active[:row], active[:col])
    return and_objects(
        row >= index_lower_bound,
        row < index_upper_bound,
        col >= index_lower_bound,
        col <= index_upper_bound,
        row_vec == call_selection_two_args(vec, vec, select_two_args_fn_obj),
        out == call_matrix_selection_two_args(matrix, matrix, select_two_args_fn_obj),
    )


def selection_two_args_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        select_two_args_fn_decl,
        selection_two_args_fn_decl,
        matrix_selection_two_args_fn_decl,
    ]


selection_two_args_inv0_grammar = InvGrammar(selection_two_args_inv0_grammar_fn, [])
selection_two_args_inv1_grammar = InvGrammar(
    selection_two_args_inv1_grammar_fn, ["row", "agg.result"]
)


def elemwise_body(
    left: Union[mlList[Int], Matrix[Int], Tensor3D[Int]],
    right: Union[mlList[Int], Matrix[Int], Tensor3D[Int]],
    compute_fn: Callable[[Int, Int], Int],
    vec_fn_name: str,
    matrix_fn_name: str,
    tensor3d_fn_name: str,
) -> Union[mlList[Int], Matrix[Int]]:
    if is_tensor3d_type(left.type) and is_tensor3d_type(right.type):
        cur = call(matrix_fn_name, Matrix[Int], left[0], right[0])
        recursed = call(tensor3d_fn_name, Tensor3D[Int], left[1:], right[1:])
        general_answer = recursed.prepend(cur)
        return ite(
            or_objects(left.len() < 1, left.len() != right.len()),
            Tensor3D.empty(Int),
            general_answer,
        )
    elif is_matrix_type(left.type) and is_matrix_type(right.type):
        cur = call(vec_fn_name, mlList[Int], left[0], right[0])
        recursed = call(matrix_fn_name, Matrix[Int], left[1:], right[1:])
        general_answer = recursed.prepend(cur)
        return ite(
            or_objects(left.len() < 1, left.len() != right.len()),
            Matrix.empty(Int),
            general_answer,
        )
    elif (
        is_list_type(left.type)
        and is_primitive_type(get_list_element_type(left.type))
        and is_list_type(right.type)
        and is_primitive_type(get_list_element_type(right.type))
    ):
        cur = compute_fn(left[0], right[0])
        recursed = call(vec_fn_name, mlList[Int], left[1:], right[1:])
        general_answer = recursed.prepend(cur)
        return ite(
            or_objects(left.len() < 1, left.len() != right.len()),
            mlList.empty(Int),
            general_answer,
        )
    raise Exception("Unsupported types for elemwise operations!")


def scalar_body(
    scalar: Int,
    vec_or_matrix: Union[mlList[Int], Matrix[Int]],
    compute_fn: Callable[[Int, Int], Int],
    vec_fn_name: str,
    matrix_fn_name: str,
) -> Union[mlList[Int], Matrix[Int]]:
    if is_matrix_type(vec_or_matrix.type):
        cur = call(vec_fn_name, mlList[Int], scalar, vec_or_matrix[0])
        recursed = call(matrix_fn_name, Matrix[Int], scalar, vec_or_matrix[1:])
        general_answer = recursed.prepend(cur)
        return ite(
            or_objects(vec_or_matrix.len() < 1), Matrix.empty(Int), general_answer
        )
    elif is_list_type(vec_or_matrix.type) and is_primitive_type(
        get_list_element_type(vec_or_matrix.type)
    ):
        cur = compute_fn(scalar, vec_or_matrix[0])
        recursed = call(vec_fn_name, mlList[Int], scalar, vec_or_matrix[1:])
        general_answer = recursed.prepend(cur)
        return ite(
            or_objects(vec_or_matrix.len() < 1), mlList.empty(Int), general_answer
        )
    raise Exception("Unsupported types for scalar operations!")


def map_body(
    vec_or_matrix: Union[mlList[Int], Matrix[Int]],
    map_fn: Callable[[Int], Int],
    vec_map_fn_name: str,
    matrix_map_fn_name: str,
) -> Union[mlList[Int], Matrix[Int]]:
    if is_matrix_type(vec_or_matrix.type):
        cur = call(vec_map_fn_name, mlList[Int], vec_or_matrix[0])
        recursed = call(matrix_map_fn_name, Matrix[Int], vec_or_matrix[1:])
        general_answer = recursed.prepend(cur)
        return ite(
            or_objects(vec_or_matrix.len() < 1), Matrix.empty(Int), general_answer
        )
    elif is_list_type(vec_or_matrix.type) and is_primitive_type(
        get_list_element_type(vec_or_matrix.type)
    ):
        cur = map_fn(vec_or_matrix[0])
        recursed = call(vec_map_fn_name, mlList[Int], vec_or_matrix[1:])
        general_answer = recursed.prepend(cur)
        return ite(
            or_objects(vec_or_matrix.len() < 1), mlList.empty(Int), general_answer
        )
    raise Exception("Unsupported types for scalar operations!")


vec_elemwise_add = fn_decl_recursive(
    VEC_ELEMWISE_ADD,
    mlList[Int],
    elemwise_body(
        left=x,
        right=y,
        compute_fn=lambda int_x, int_y: int_x + int_y,
        vec_fn_name=VEC_ELEMWISE_ADD,
        matrix_fn_name=MATRIX_ELEMWISE_ADD,
        tensor3d_fn_name=TENSOR3D_ELEMWISE_ADD,
    ),
    x,
    y,
)
matrix_elemwise_add = fn_decl_recursive(
    MATRIX_ELEMWISE_ADD,
    Matrix[Int],
    elemwise_body(
        left=matrix_x,
        right=matrix_y,
        compute_fn=lambda int_x, int_y: int_x + int_y,
        vec_fn_name=VEC_ELEMWISE_ADD,
        matrix_fn_name=MATRIX_ELEMWISE_ADD,
        tensor3d_fn_name=TENSOR3D_ELEMWISE_ADD,
    ),
    matrix_x,
    matrix_y,
)
tensor3d_elemwise_add = fn_decl_recursive(
    TENSOR3D_ELEMWISE_ADD,
    Tensor3D[Int],
    elemwise_body(
        left=tensor3d_x,
        right=tensor3d_y,
        compute_fn=lambda int_x, int_y: int_x + int_y,
        vec_fn_name=VEC_ELEMWISE_ADD,
        matrix_fn_name=MATRIX_ELEMWISE_ADD,
        tensor3d_fn_name=TENSOR3D_ELEMWISE_ADD,
    ),
    tensor3d_x,
    tensor3d_y,
)

vec_elemwise_sub = fn_decl_recursive(
    VEC_ELEMWISE_SUB,
    mlList[Int],
    elemwise_body(
        left=x,
        right=y,
        compute_fn=lambda int_x, int_y: int_x - int_y,
        vec_fn_name=VEC_ELEMWISE_SUB,
        matrix_fn_name=MATRIX_ELEMWISE_SUB,
        tensor3d_fn_name=TENSOR3D_ELEMWISE_SUB,
    ),
    x,
    y,
)
matrix_elemwise_sub = fn_decl_recursive(
    MATRIX_ELEMWISE_SUB,
    Matrix[Int],
    elemwise_body(
        left=matrix_x,
        right=matrix_y,
        compute_fn=lambda int_x, int_y: int_x + int_y,
        vec_fn_name=VEC_ELEMWISE_SUB,
        matrix_fn_name=MATRIX_ELEMWISE_SUB,
        tensor3d_fn_name=TENSOR3D_ELEMWISE_SUB,
    ),
    matrix_x,
    matrix_y,
)
tensor3d_elemwise_sub = fn_decl_recursive(
    TENSOR3D_ELEMWISE_SUB,
    Tensor3D[Int],
    elemwise_body(
        left=tensor3d_x,
        right=tensor3d_y,
        compute_fn=lambda int_x, int_y: int_x + int_y,
        vec_fn_name=VEC_ELEMWISE_SUB,
        matrix_fn_name=MATRIX_ELEMWISE_SUB,
        tensor3d_fn_name=TENSOR3D_ELEMWISE_SUB,
    ),
    tensor3d_x,
    tensor3d_y,
)

vec_elemwise_mul = fn_decl_recursive(
    VEC_ELEMWISE_MUL,
    mlList[Int],
    elemwise_body(
        left=x,
        right=y,
        compute_fn=lambda int_x, int_y: int_x * int_y,
        vec_fn_name=VEC_ELEMWISE_MUL,
        matrix_fn_name=MATRIX_ELEMWISE_MUL,
        tensor3d_fn_name=TENSOR3D_ELEMWISE_MUL,
    ),
    x,
    y,
)
matrix_elemwise_mul = fn_decl_recursive(
    MATRIX_ELEMWISE_MUL,
    Matrix[Int],
    elemwise_body(
        left=matrix_x,
        right=matrix_y,
        compute_fn=lambda int_x, int_y: int_x * int_y,
        vec_fn_name=VEC_ELEMWISE_MUL,
        matrix_fn_name=MATRIX_ELEMWISE_MUL,
        tensor3d_fn_name=TENSOR3D_ELEMWISE_MUL,
    ),
    matrix_x,
    matrix_y,
)
tensor3d_elemwise_mul = fn_decl_recursive(
    TENSOR3D_ELEMWISE_MUL,
    Tensor3D[Int],
    elemwise_body(
        left=tensor3d_x,
        right=tensor3d_y,
        compute_fn=lambda int_x, int_y: int_x + int_y,
        vec_fn_name=VEC_ELEMWISE_MUL,
        matrix_fn_name=MATRIX_ELEMWISE_MUL,
        tensor3d_fn_name=TENSOR3D_ELEMWISE_MUL,
    ),
    tensor3d_x,
    tensor3d_y,
)

vec_elemwise_div = fn_decl_recursive(
    VEC_ELEMWISE_DIV,
    mlList[Int],
    elemwise_body(
        left=x,
        right=y,
        compute_fn=lambda int_x, int_y: int_x // int_y,
        vec_fn_name=VEC_ELEMWISE_DIV,
        matrix_fn_name=MATRIX_ELEMWISE_DIV,
        tensor3d_fn_name=TENSOR3D_ELEMWISE_DIV,
    ),
    x,
    y,
)
matrix_elemwise_div = fn_decl_recursive(
    MATRIX_ELEMWISE_DIV,
    Matrix[Int],
    elemwise_body(
        left=matrix_x,
        right=matrix_y,
        compute_fn=lambda int_x, int_y: int_x // int_y,
        vec_fn_name=VEC_ELEMWISE_DIV,
        matrix_fn_name=MATRIX_ELEMWISE_DIV,
        tensor3d_fn_name=TENSOR3D_ELEMWISE_DIV,
    ),
    matrix_x,
    matrix_y,
)
tensor3d_elemwise_div = fn_decl_recursive(
    TENSOR3D_ELEMWISE_DIV,
    Tensor3D[Int],
    elemwise_body(
        left=tensor3d_x,
        right=tensor3d_y,
        compute_fn=lambda int_x, int_y: int_x + int_y,
        vec_fn_name=VEC_ELEMWISE_DIV,
        matrix_fn_name=MATRIX_ELEMWISE_DIV,
        tensor3d_fn_name=TENSOR3D_ELEMWISE_DIV,
    ),
    tensor3d_x,
    tensor3d_y,
)

vec_scalar_add = fn_decl_recursive(
    VEC_SCALAR_ADD,
    mlList[Int],
    scalar_body(
        scalar=a,
        vec_or_matrix=x,
        compute_fn=lambda scalar, int_x: scalar + int_x,
        vec_fn_name=VEC_SCALAR_ADD,
        matrix_fn_name=MATRIX_SCALAR_ADD,
    ),
    a,
    x,
)
matrix_scalar_add = fn_decl_recursive(
    MATRIX_SCALAR_ADD,
    Matrix[Int],
    scalar_body(
        scalar=a,
        vec_or_matrix=matrix_x,
        compute_fn=lambda scalar, int_x: scalar + int_x,
        vec_fn_name=VEC_SCALAR_ADD,
        matrix_fn_name=MATRIX_SCALAR_ADD,
    ),
    a,
    matrix_x,
)

vec_scalar_mul = fn_decl_recursive(
    VEC_SCALAR_MUL,
    mlList[Int],
    scalar_body(
        scalar=a,
        vec_or_matrix=x,
        compute_fn=lambda scalar, int_x: scalar * int_x,
        vec_fn_name=VEC_SCALAR_MUL,
        matrix_fn_name=MATRIX_SCALAR_MUL,
    ),
    a,
    x,
)
matrix_scalar_mul = fn_decl_recursive(
    MATRIX_SCALAR_MUL,
    Matrix[Int],
    scalar_body(
        scalar=a,
        vec_or_matrix=matrix_x,
        compute_fn=lambda scalar, int_x: scalar * int_x,
        vec_fn_name=VEC_SCALAR_MUL,
        matrix_fn_name=MATRIX_SCALAR_MUL,
    ),
    a,
    matrix_x,
)

vec_scalar_div = fn_decl_recursive(
    VEC_SCALAR_DIV,
    mlList[Int],
    scalar_body(
        scalar=a,
        vec_or_matrix=x,
        compute_fn=lambda scalar, int_x: int_x // scalar,
        vec_fn_name=VEC_SCALAR_DIV,
        matrix_fn_name=MATRIX_SCALAR_DIV,
    ),
    a,
    x,
)
scalar_vec_div = fn_decl_recursive(
    SCALAR_VEC_DIV,
    mlList[Int],
    scalar_body(
        scalar=a,
        vec_or_matrix=x,
        compute_fn=lambda scalar, int_x: scalar // int_x,
        vec_fn_name=SCALAR_VEC_DIV,
        matrix_fn_name=SCALAR_MATRIX_DIV,
    ),
    a,
    x,
)
matrix_scalar_div = fn_decl_recursive(
    MATRIX_SCALAR_DIV,
    Matrix[Int],
    scalar_body(
        scalar=a,
        vec_or_matrix=matrix_x,
        compute_fn=lambda scalar, int_x: int_x // scalar,
        vec_fn_name=VEC_SCALAR_DIV,
        matrix_fn_name=MATRIX_SCALAR_DIV,
    ),
    a,
    matrix_x,
)
scalar_matrix_div = fn_decl_recursive(
    SCALAR_MATRIX_DIV,
    Matrix[Int],
    scalar_body(
        scalar=a,
        vec_or_matrix=matrix_x,
        compute_fn=lambda scalar, int_x: scalar // int_x,
        vec_fn_name=SCALAR_VEC_DIV,
        matrix_fn_name=SCALAR_MATRIX_DIV,
    ),
    a,
    matrix_x,
)

vec_scalar_sub = fn_decl_recursive(
    VEC_SCALAR_SUB,
    mlList[Int],
    scalar_body(
        scalar=a,
        vec_or_matrix=x,
        compute_fn=lambda scalar, int_x: int_x - scalar,
        vec_fn_name=VEC_SCALAR_SUB,
        matrix_fn_name=MATRIX_SCALAR_SUB,
    ),
    a,
    x,
)
scalar_vec_sub = fn_decl_recursive(
    SCALAR_VEC_SUB,
    mlList[Int],
    scalar_body(
        scalar=a,
        vec_or_matrix=x,
        compute_fn=lambda scalar, int_x: scalar - int_x,
        vec_fn_name=SCALAR_VEC_SUB,
        matrix_fn_name=SCALAR_MATRIX_SUB,
    ),
    a,
    x,
)
matrix_scalar_sub = fn_decl_recursive(
    MATRIX_SCALAR_SUB,
    Matrix[Int],
    scalar_body(
        scalar=a,
        vec_or_matrix=matrix_x,
        compute_fn=lambda scalar, int_x: int_x - scalar,
        vec_fn_name=VEC_SCALAR_SUB,
        matrix_fn_name=MATRIX_SCALAR_SUB,
    ),
    a,
    matrix_x,
)
scalar_matrix_sub = fn_decl_recursive(
    SCALAR_MATRIX_SUB,
    Matrix[Int],
    scalar_body(
        scalar=a,
        vec_or_matrix=matrix_x,
        compute_fn=lambda scalar, int_x: int_x - scalar,
        vec_fn_name=SCALAR_VEC_SUB,
        matrix_fn_name=SCALAR_MATRIX_SUB,
    ),
    a,
    matrix_x,
)


def vec_map_body(vec: mlList[Int], map_fn: Fn[tuple[Int, Int]]) -> mlList[Int]:
    cur = call_value(map_fn, vec[0])
    recursed = call_vec_map(vec[1:], map_fn)
    return ite(vec.len() < 1, mlList.empty(Int), recursed.prepend(cur))


vec_map = fn_decl_recursive(
    VEC_MAP,
    mlList[Int],
    vec_map_body(x, map_int_to_int_fn_obj),
    x,
    map_int_to_int_fn_obj,
)

# Uninterpreted functions
# TODO: this is returning a random prime
vec_vec_to_vec_target_lang = [
    vec_elemwise_add,
    vec_elemwise_sub,
    vec_elemwise_mul,
    vec_elemwise_div,
]
matrix_matrix_to_matrix_target_lang = [
    matrix_elemwise_add,
    matrix_elemwise_sub,
    matrix_elemwise_mul,
    matrix_elemwise_div,
]
scalar_vec_to_vec_target_lang = [
    vec_scalar_add,
    vec_scalar_sub,
    vec_scalar_mul,
    vec_scalar_div,
    scalar_vec_sub,
    scalar_vec_div,
]
scalar_matrix_to_matrix_target_lang = [
    matrix_scalar_add,
    matrix_scalar_sub,
    matrix_scalar_mul,
    matrix_scalar_div,
    scalar_matrix_sub,
    scalar_matrix_div,
]
vec_to_int_target_lang = [reduce_max, reduce_sum, reduce_mul]
matrix_vec_to_vec_target_lang = [matrix_vec_mul, vec_elemwise_mul, reduce_sum]
vec_to_vec_target_lang = [vec_map, map_int_to_int]


n = Int("n")
integer_exp_fn_name = "integer_exp"
integer_exp_body = ite(n <= 0, Int(1), (call(integer_exp_fn_name, Int, n - 1) * 3) % 64)
integer_exp_fn_decl = fn_decl_recursive(integer_exp_fn_name, Int, integer_exp_body, n)

guess = Int("guess")
integer_sqrt_helper_fn_name = "integer_sqrt_helper"
integer_sqrt_helper_body = ite(
    or_objects(guess == 0, guess == 1, guess > 64),
    Int(1),
    ite(
        guess == n // guess,
        guess,
        call(integer_sqrt_helper_fn_name, Int, n, (guess + n // guess) // 2),
    ),
)
integer_sqrt_helper_fn_decl = fn_decl_recursive(
    integer_sqrt_helper_fn_name,
    Int,
    integer_sqrt_helper_body,
    n,
    guess,
)

integer_sqrt_fn_name = "integer_sqrt"
integer_sqrt_fn_decl = fn_decl(
    integer_sqrt_fn_name, Int, call(integer_sqrt_helper_fn_name, Int, n // 2, n), n
)


def get_matrix_computation_general_search_space(
    depth: int, int_vars: List[Int], relaxed: bool
) -> Tuple[
    InvGrammar,
    InvGrammar,
    Callable[[List[Object], List[Object], List[Object]], List[Object]],
    Callable[[], List[Union[FnDecl, FnDeclRecursive]]],
    List[Synth],
]:
    # Target language
    def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
        return [
            matrix_vec_mul,
            reduce_sum,
            *vec_to_vec_target_lang,
            *scalar_vec_to_vec_target_lang,
            *scalar_matrix_to_matrix_target_lang,
            *vec_vec_to_vec_target_lang,
            *matrix_matrix_to_matrix_target_lang,
        ]

    fns_synths = [get_map_int_to_int_synth()]

    # inv0 grammar
    def inv0_grammar_fn(
        writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
    ) -> Bool:
        out, col, pixel, row, row_vec = writes
        base, active = reads
        lower_bound = Int(0)
        upper_bound = base.len()
        int_var = choose(lower_bound, upper_bound, row, *int_vars).maybe_relaxed(
            relaxed
        )
        slice_index = get_int_expr_eq_or_below_depth(int_var, depth)
        matrix = choose(base, active)
        matrix = matrix[slice_index:slice_index].col_slice(slice_index, slice_index)
        matrix = choose(matrix, matrix.transpose())
        return and_objects(
            row >= lower_bound.maybe_relaxed(relaxed),
            row <= upper_bound.maybe_relaxed(relaxed),
            out
            == get_matrix_or_vec_expr_eq_or_below_depth(
                matrix_or_vec_var=matrix, int_var=int_var, depth=depth
            ),
        )

    def inv1_grammar_fn(
        writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
    ) -> Bool:
        col, pixel, row_vec = writes
        out, row = in_scope
        base, active = reads
        outer_loop_lower_bound = Int(0)
        outer_loop_upper_bound = base.len()
        inner_loop_lower_bound = Int(0)
        inner_loop_upper_bound = base[0].len()
        int_var = choose(
            Int(0), base.len(), base[0].len(), row, col, *int_vars
        ).maybe_relaxed(relaxed)
        slice_index = get_int_expr_eq_or_below_depth(int_var, depth)
        matrix = choose(base, active)
        matrix = matrix[slice_index:slice_index].col_slice(slice_index, slice_index)
        matrix = choose(matrix, matrix.transpose())
        vec = matrix[slice_index]
        return and_objects(
            row >= outer_loop_lower_bound,
            row <= outer_loop_upper_bound,
            col >= inner_loop_lower_bound,
            col <= inner_loop_upper_bound,
            row_vec
            == get_matrix_or_vec_expr_eq_or_below_depth(
                matrix_or_vec_var=vec,
                int_var=int_var,
                depth=depth,
                additional_matrix=matrix,
            ),
            out
            == get_matrix_or_vec_expr_eq_or_below_depth(
                matrix_or_vec_var=matrix, int_var=int_var, depth=depth
            ),
        )

    def ps_grammar_fn(
        writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
    ) -> Bool:
        ret_val = writes[0]
        base, active = reads
        matrix = choose(base, active)
        int_var = choose(Int(0), base.len(), base[0].len(), *int_vars).maybe_relaxed(
            relaxed
        )
        slice_index = get_int_expr_eq_or_below_depth(int_var, depth)
        matrix = matrix[slice_index:slice_index].col_slice(slice_index, slice_index)
        matrix = choose(matrix, matrix.transpose())
        return ret_val == get_matrix_or_vec_expr_eq_or_below_depth(
            matrix_or_vec_var=matrix, int_var=int_var, depth=depth
        )

    inv0_grammar = InvGrammar(inv0_grammar_fn, [])
    inv1_grammar = InvGrammar(inv1_grammar_fn, ["row", "agg.result"])
    return inv0_grammar, inv1_grammar, ps_grammar_fn, target_lang, fns_synths


def get_matrix_computation_holing_search_space(
    hole_body: Callable[[TensorT], TensorT]
) -> Tuple[
    InvGrammar,
    InvGrammar,
    Callable[[List[Object], List[Object], List[Object]], List[Object]],
    Callable[[], List[Union[FnDecl, FnDeclRecursive]]],
    List[Synth],
]:
    outer_loop_index_first_fn_name = "OUTER_LOOP_INDEX_FIRST"
    (
        outer_loop_index_first_fn_decl,
        outer_loop_index_first_synth,
        is_outer_loop_index_first,
    ) = get_no_arg_bool_fn(outer_loop_index_first_fn_name)

    # Target language
    def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
        return [
            outer_loop_index_first_fn_decl,
            *scalar_vec_to_vec_target_lang,
            *scalar_matrix_to_matrix_target_lang,
            *vec_vec_to_vec_target_lang,
            *matrix_matrix_to_matrix_target_lang,
        ]

    fns_synths = [outer_loop_index_first_synth]

    # inv0 grammar
    def inv0_grammar_fn(
        writes: List[Object],
        reads: List[Object],
        in_scope: List[Object],
        relaxed_grammar: bool,
    ) -> Bool:
        out, col, pixel, row, row_vec = writes
        base, active = reads
        int_vars = [row, col]
        matrix = choose(base, active)
        matrix = ite(
            is_outer_loop_index_first(),  # Then outer loop has to be over row
            matrix[:row],
            matrix.col_slice(0, row),
        )
        matrix = choose(matrix, matrix.transpose())
        return and_objects(
            row >= 0,
            row <= base.len(),
            out == hole_body(matrix),
        )

    def inv1_grammar_fn(
        writes: List[Object],
        reads: List[Object],
        in_scope: List[Object],
        relaxed_grammar: bool,
    ) -> Bool:
        col, pixel, row_vec = writes
        out, row = in_scope
        base, active = reads
        int_vars = [row, col]
        matrix = choose(base, active)
        outer_loop_matrix = ite(
            is_outer_loop_index_first(),  # Then outer loop has to be over row
            matrix[:row],
            matrix.col_slice(0, row),
        )
        outer_loop_matrix = choose(outer_loop_matrix, outer_loop_matrix.transpose())
        inner_loop_vec = ite(
            is_outer_loop_index_first(),
            matrix[row][:col],
            matrix[:col].col_vec(row),
        )
        return and_objects(
            row >= 0,
            row <= base.len(),
            col >= 0,
            col <= base[0].len(),
            row_vec == hole_body(inner_loop_vec),
            out == hole_body(outer_loop_matrix),
        )

    def ps_grammar_fn(
        writes: List[Object],
        reads: List[Object],
        in_scope: List[Object],
        relaxed_grammar: bool,
    ) -> Bool:
        ret_val = writes[0]
        base, active = reads
        matrix = choose(base, active)
        matrix = choose(matrix, matrix.transpose())
        return ret_val == hole_body(matrix)

    inv0_grammar = InvGrammar(inv0_grammar_fn, [])
    inv1_grammar = InvGrammar(inv1_grammar_fn, ["row", "agg.result"])
    return inv0_grammar, inv1_grammar, ps_grammar_fn, target_lang, fns_synths


def get_matrix_select_general_search_space(
    driver: Driver, depth: int, cons: Int, relaxed: bool
) -> Tuple[
    InvGrammar,
    InvGrammar,
    Callable[[List[Object], List[Object], List[Object]], List[Object]],
    Callable[[], List[Union[FnDecl, FnDeclRecursive]]],
    List[Synth],
]:
    int_x, int_y = Int("int_x"), Int("int_y")
    driver.add_var_objects([int_x, int_y])
    int_var = choose(int_x, int_y, *cons)
    select_synth = synth(
        SELECT_TWO_ARGS, get_cond_expr_eq_or_below_depth(int_var, depth), int_x, int_y
    )

    # Target language
    def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
        return [
            matrix_vec_mul,
            reduce_sum,
            select_two_args_fn_decl,
            selection_two_args_fn_decl,
            matrix_selection_two_args_fn_decl,
            *vec_to_vec_target_lang,
            *scalar_vec_to_vec_target_lang,
            *scalar_matrix_to_matrix_target_lang,
            *vec_vec_to_vec_target_lang,
            *matrix_matrix_to_matrix_target_lang,
        ]

    # Functions to synthesize
    fns_synths = [select_synth, get_map_int_to_int_synth()]

    # inv0 grammar
    def inv0_grammar_fn(
        writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
    ) -> Bool:
        writes_by_name = {write_var.var_name(): write_var for write_var in writes}
        out = writes_by_name["agg.result"]
        col = writes_by_name["col"]
        row = writes_by_name["row"]

        reads_by_name = {read_var.var_name(): read_var for read_var in reads}
        base = reads_by_name["base"]
        active = reads_by_name["active"]

        matrix = choose(base, active)
        lower_bound = Int(0)
        upper_bound = base.len()
        int_var = choose(Int(0), base.len(), base[0].len(), row).maybe_relaxed(relaxed)
        slice_index = get_int_expr_eq_or_below_depth(int_var, depth)
        matrix = matrix[slice_index:slice_index].col_slice(slice_index, slice_index)
        matrix = choose(matrix, matrix.transpose())
        return and_objects(
            row >= lower_bound.maybe_relaxed(relaxed),
            row <= upper_bound.maybe_relaxed(relaxed),
            out
            == call_matrix_selection_two_args(matrix, matrix, select_two_args_fn_obj),
        )

    def inv1_grammar_fn(
        writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
    ) -> Bool:
        writes_by_name = {write_var.var_name(): write_var for write_var in writes}
        col = writes_by_name["col"]
        row_vec = writes_by_name["row_vec"]

        in_scope_by_name = {
            in_scope_var.var_name(): in_scope_var for in_scope_var in in_scope
        }
        out = in_scope_by_name["agg.result"]
        row = in_scope_by_name["row"]

        reads_by_name = {read_var.var_name(): read_var for read_var in reads}
        base = reads_by_name["base"]
        active = reads_by_name["active"]

        matrix = choose(base, active)
        int_var = choose(Int(0), base.len(), base[0].len(), row, col).maybe_relaxed(
            relaxed
        )
        slice_index = get_int_expr_eq_or_below_depth(int_var, depth)
        matrix = matrix[slice_index:slice_index].col_slice(slice_index, slice_index)
        matrix = choose(matrix, matrix.transpose())
        vec = matrix[slice_index]

        outer_loop_lower_bound = Int(0)
        outer_loop_upper_bound = base.len()
        inner_loop_lower_bound = Int(0)
        inner_loop_upper_bound = base[0].len()

        return and_objects(
            row >= outer_loop_lower_bound.maybe_relaxed(relaxed),
            row <= outer_loop_upper_bound.maybe_relaxed(relaxed),
            col >= inner_loop_lower_bound.maybe_relaxed(relaxed),
            col <= inner_loop_upper_bound.maybe_relaxed(relaxed),
            row_vec == call_selection_two_args(vec, vec, select_two_args_fn_obj),
            out
            == call_matrix_selection_two_args(matrix, matrix, select_two_args_fn_obj),
        )

    def ps_grammar_fn(
        writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
    ) -> Bool:
        ret_val = writes[0]
        reads_by_name = {read_var.var_name(): read_var for read_var in reads}
        base = reads_by_name["base"]
        active = reads_by_name["active"]
        int_var = choose(Int(0), base.len(), base[0].len()).maybe_relaxed(relaxed)
        slice_index = get_int_expr_eq_or_below_depth(int_var, depth)
        matrix = choose(base, active)
        matrix = choose(matrix, matrix.transpose())
        matrix = matrix[slice_index:slice_index].col_slice(slice_index, slice_index)
        return ret_val == call_matrix_selection_two_args(
            matrix, matrix, select_two_args_fn_obj
        )

    inv0_grammar = InvGrammar(inv0_grammar_fn, [])
    inv1_grammar = InvGrammar(inv1_grammar_fn, ["row", "agg.result"])
    return inv0_grammar, inv1_grammar, ps_grammar_fn, target_lang, fns_synths


def get_matrix_select_holing_search_space(
    driver: Driver, hole_body: Callable[[Int], Int]
) -> Tuple[
    InvGrammar,
    InvGrammar,
    Callable[[List[Object], List[Object], List[Object]], List[Object]],
    Callable[[], List[Union[FnDecl, FnDeclRecursive]]],
    List[Synth],
]:
    select_synth = get_select_synth_from_hole(driver, hole_body)
    outer_loop_index_first_fn_name = "OUTER_LOOP_INDEX_FIRST"
    (
        outer_loop_index_first_fn_decl,
        outer_loop_index_first_synth,
        is_outer_loop_index_first,
    ) = get_no_arg_bool_fn(outer_loop_index_first_fn_name)

    # Target language
    def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
        return [
            outer_loop_index_first_fn_decl,
            select_two_args_fn_decl,
            selection_two_args_fn_decl,
            matrix_selection_two_args_fn_decl,
        ]

    # Functions to synthesize
    fns_synths = [select_synth, outer_loop_index_first_synth]

    # inv0 grammar
    def inv0_grammar_fn(
        writes: List[Object],
        reads: List[Object],
        in_scope: List[Object],
        relaxed_grammar: bool,
    ) -> Bool:
        writes_by_name = {write_var.var_name(): write_var for write_var in writes}
        out = writes_by_name["agg.result"]
        col = writes_by_name["col"]
        row = writes_by_name["row"]
        reads_by_name = {read_var.var_name(): read_var for read_var in reads}
        base = reads_by_name["base"]
        active = reads_by_name["active"]

        matrix = choose(base, active)
        matrix = ite(
            is_outer_loop_index_first(),  # Then outer loop has to be over row
            matrix[:row],
            matrix.col_slice(0, row),
        )
        matrix = choose(matrix, matrix.transpose())
        return and_objects(
            row >= 0,
            row <= base.len(),
            out
            == call_matrix_selection_two_args(matrix, matrix, select_two_args_fn_obj),
        )

    def inv1_grammar_fn(
        writes: List[Object],
        reads: List[Object],
        in_scope: List[Object],
        relaxed_grammar: bool,
    ) -> Bool:
        writes_by_name = {write_var.var_name(): write_var for write_var in writes}
        col = writes_by_name["col"]
        row_vec = writes_by_name["row_vec"]
        in_scope_by_name = {
            in_scope_var.var_name(): in_scope_var for in_scope_var in in_scope
        }
        out = in_scope_by_name["agg.result"]
        row = in_scope_by_name["row"]
        reads_by_name = {read_var.var_name(): read_var for read_var in reads}
        base = reads_by_name["base"]
        active = reads_by_name["active"]

        matrix = choose(base, active)
        outer_loop_matrix = ite(
            is_outer_loop_index_first(),  # Then outer loop has to be over row
            matrix[:row],
            matrix.col_slice(0, row),
        )
        outer_loop_matrix = choose(outer_loop_matrix, outer_loop_matrix.transpose())
        inner_loop_vec = ite(
            is_outer_loop_index_first(),
            matrix[row][:col],
            matrix[:col].col_vec(row),
        )
        return and_objects(
            row >= 0,
            row <= base.len(),
            col >= 0,
            col <= base[0].len(),
            row_vec
            == call_selection_two_args(
                inner_loop_vec, inner_loop_vec, select_two_args_fn_obj
            ),
            out
            == call_matrix_selection_two_args(
                outer_loop_matrix, outer_loop_matrix, select_two_args_fn_obj
            ),
        )

    def ps_grammar_fn(
        writes: List[Object],
        reads: List[Object],
        in_scope: List[Object],
        relaxed_grammar: bool,
    ) -> Bool:
        ret_val = writes[0]
        reads_by_name = {read_var.var_name(): read_var for read_var in reads}
        base = reads_by_name["base"]
        active = reads_by_name["active"]
        matrix = choose(base, active)
        matrix = choose(matrix, matrix.transpose())
        return ret_val == call_matrix_selection_two_args(
            matrix, matrix, select_two_args_fn_obj
        )

    inv0_grammar = InvGrammar(inv0_grammar_fn, [])
    inv1_grammar = InvGrammar(inv1_grammar_fn, ["row", "agg.result"])
    return inv0_grammar, inv1_grammar, ps_grammar_fn, target_lang, fns_synths


def get_dissolve_holing_search_space(
    driver: Driver,
) -> Tuple[
    InvGrammar,
    InvGrammar,
    Callable[[List[Object], List[Object], List[Object]], List[Object]],
    Callable[[], List[Union[FnDecl, FnDeclRecursive]]],
    List[Synth],
]:
    int_var = choose(int_x, int_y, opacity, rand_cons)
    dissolve_select_synth = synth(
        DISSOLVE_SELECT_TWO_ARGS,
        dissolve_blend_8_hole_body(int_var),
        int_x,
        int_y,
        opacity,
        rand_cons,
    )
    driver.add_var_objects([int_x, int_y, opacity, rand_cons])

    outer_loop_index_first_fn_name = "OUTER_LOOP_INDEX_FIRST"
    (
        outer_loop_index_first_fn_decl,
        outer_loop_index_first_synth,
        is_outer_loop_index_first,
    ) = get_no_arg_bool_fn(outer_loop_index_first_fn_name)

    # Target language
    def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
        return [
            outer_loop_index_first_fn_decl,
            dissolve_select_two_args_fn_decl,
            dissolve_selection_two_args_fn_decl,
            dissolve_matrix_selection_two_args_fn_decl,
        ]

    fns_synths = [dissolve_select_synth, outer_loop_index_first_synth]

    # inv0 grammar
    def inv0_grammar_fn(
        writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
    ) -> Bool:
        writes_by_name = {write_var.var_name(): write_var for write_var in writes}
        out = writes_by_name["agg.result"]
        col = writes_by_name["col"]
        row = writes_by_name["row"]

        reads_by_name = {read_var.var_name(): read_var for read_var in reads}
        base = reads_by_name["base"]
        active = reads_by_name["active"]
        opacity = reads_by_name["opacity"]
        rand_cons = reads_by_name["rand_cons"]

        matrix = choose(base, active)
        matrix = ite(
            is_outer_loop_index_first(),  # Then outer loop has to be over row
            matrix[:row],
            matrix.col_slice(0, row),
        )
        matrix = choose(matrix, matrix.transpose())
        return and_objects(
            row >= 0,
            row <= base.len(),
            out
            == call_dissolve_matrix_selection_two_args(
                matrix, matrix, opacity, rand_cons, dissolve_select_two_args_fn_obj
            ),
        )

    def inv1_grammar_fn(
        writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
    ) -> Bool:
        writes_by_name = {write_var.var_name(): write_var for write_var in writes}
        col = writes_by_name["col"]
        row_vec = writes_by_name["row_vec"]

        in_scope_by_name = {
            in_scope_var.var_name(): in_scope_var for in_scope_var in in_scope
        }
        out = in_scope_by_name["agg.result"]
        row = in_scope_by_name["row"]

        reads_by_name = {read_var.var_name(): read_var for read_var in reads}
        base = reads_by_name["base"]
        active = reads_by_name["active"]
        opacity = reads_by_name["opacity"]
        rand_cons = reads_by_name["rand_cons"]

        matrix = choose(base, active)
        outer_loop_matrix = ite(
            is_outer_loop_index_first(),  # Then outer loop has to be over row
            matrix[:row],
            matrix.col_slice(0, row),
        )
        outer_loop_matrix = choose(outer_loop_matrix, outer_loop_matrix.transpose())
        inner_loop_vec = ite(
            is_outer_loop_index_first(),
            matrix[row][:col],
            matrix[:col].col_vec(row),
        )
        return and_objects(
            row >= 0,
            row <= base.len(),
            col >= 0,
            col <= base[0].len(),
            row_vec
            == call_dissolve_selection_two_args(
                inner_loop_vec,
                inner_loop_vec,
                opacity,
                rand_cons,
                dissolve_select_two_args_fn_obj,
            ),
            out
            == call_dissolve_matrix_selection_two_args(
                outer_loop_matrix,
                outer_loop_matrix,
                opacity,
                rand_cons,
                dissolve_select_two_args_fn_obj,
            ),
        )

    def ps_grammar_fn(
        writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
    ) -> Bool:
        ret_val = writes[0]
        reads_by_name = {read_var.var_name(): read_var for read_var in reads}
        base = reads_by_name["base"]
        active = reads_by_name["active"]
        opacity = reads_by_name["opacity"]
        rand_cons = reads_by_name["rand_cons"]
        matrix = choose(base, active)
        matrix = choose(matrix, matrix.transpose())
        return ret_val == call_dissolve_matrix_selection_two_args(
            matrix, matrix, opacity, rand_cons, dissolve_select_two_args_fn_obj
        )

    inv0_grammar = InvGrammar(inv0_grammar_fn, [])
    inv1_grammar = InvGrammar(inv1_grammar_fn, ["row", "agg.result"])
    return inv0_grammar, inv1_grammar, ps_grammar_fn, target_lang, fns_synths


def get_dissolve_general_search_space(
    driver: Driver, depth: int, relaxed: bool
) -> Tuple[
    InvGrammar,
    InvGrammar,
    Callable[[List[Object], List[Object], List[Object]], List[Object]],
    Callable[[], List[Union[FnDecl, FnDeclRecursive]]],
    List[Synth],
]:
    int_var = choose(int_x, int_y, opacity, rand_cons)
    dissolve_select_synth = synth(
        DISSOLVE_SELECT_TWO_ARGS,
        get_int_expr_eq_or_below_depth(var=int_var, depth=depth),
        int_x,
        int_y,
        opacity,
        rand_cons,
    )
    driver.add_var_objects([int_x, int_y, opacity, rand_cons])

    # Target language
    def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
        return [
            matrix_vec_mul,
            reduce_sum,
            dissolve_select_two_args_fn_decl,
            dissolve_selection_two_args_fn_decl,
            dissolve_matrix_selection_two_args_fn_decl,
            *vec_to_vec_target_lang,
            *scalar_vec_to_vec_target_lang,
            *scalar_matrix_to_matrix_target_lang,
            *vec_vec_to_vec_target_lang,
            *matrix_matrix_to_matrix_target_lang,
        ]

    # Functions to synthesize
    fns_synths = [dissolve_select_synth, get_map_int_to_int_synth()]

    # inv0 grammar
    def inv0_grammar_fn(
        writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
    ) -> Bool:
        writes_by_name = {write_var.var_name(): write_var for write_var in writes}
        out = writes_by_name["agg.result"]
        col = writes_by_name["col"]
        row = writes_by_name["row"]

        reads_by_name = {read_var.var_name(): read_var for read_var in reads}
        base = reads_by_name["base"]
        active = reads_by_name["active"]
        opacity = reads_by_name["opacity"]
        rand_cons = reads_by_name["rand_cons"]

        matrix = choose(base, active)
        lower_bound = Int(0)
        upper_bound = base.len()
        slice_index = choose(lower_bound, upper_bound, row).maybe_relaxed(relaxed)
        matrix = matrix[slice_index:slice_index].col_slice(slice_index, slice_index)
        matrix = choose(matrix, matrix.transpose())
        return and_objects(
            row >= lower_bound.maybe_relaxed(relaxed),
            row <= upper_bound.maybe_relaxed(relaxed),
            out
            == call_dissolve_matrix_selection_two_args(
                matrix, matrix, opacity, rand_cons, dissolve_select_two_args_fn_obj
            ),
        )

    def inv1_grammar_fn(
        writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
    ) -> Bool:
        writes_by_name = {write_var.var_name(): write_var for write_var in writes}
        col = writes_by_name["col"]
        row_vec = writes_by_name["row_vec"]

        in_scope_by_name = {
            in_scope_var.var_name(): in_scope_var for in_scope_var in in_scope
        }
        out = in_scope_by_name["agg.result"]
        row = in_scope_by_name["row"]

        reads_by_name = {read_var.var_name(): read_var for read_var in reads}
        base = reads_by_name["base"]
        active = reads_by_name["active"]
        opacity = reads_by_name["opacity"]
        rand_cons = reads_by_name["rand_cons"]

        matrix = choose(base, active)
        slice_index = choose(Int(0), base.len(), base[0].len(), row, col).maybe_relaxed(
            relaxed
        )
        matrix = matrix[slice_index:slice_index].col_slice(slice_index, slice_index)
        matrix = choose(matrix, matrix.transpose())
        vec = matrix[slice_index]

        outer_loop_lower_bound = Int(0)
        outer_loop_upper_bound = base.len()
        inner_loop_lower_bound = Int(0)
        inner_loop_upper_bound = base[0].len()

        return and_objects(
            row >= outer_loop_lower_bound.maybe_relaxed(relaxed),
            row <= outer_loop_upper_bound.maybe_relaxed(relaxed),
            col >= inner_loop_lower_bound.maybe_relaxed(relaxed),
            col <= inner_loop_upper_bound.maybe_relaxed(relaxed),
            row_vec
            == call_dissolve_selection_two_args(
                vec, vec, opacity, rand_cons, dissolve_select_two_args_fn_obj
            ),
            out
            == call_dissolve_matrix_selection_two_args(
                matrix, matrix, opacity, rand_cons, dissolve_select_two_args_fn_obj
            ),
        )

    def ps_grammar_fn(
        writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
    ) -> Bool:
        ret_val = writes[0]
        reads_by_name = {read_var.var_name(): read_var for read_var in reads}
        base = reads_by_name["base"]
        active = reads_by_name["active"]
        opacity = reads_by_name["opacity"]
        rand_cons = reads_by_name["rand_cons"]
        slice_index = choose(Int(0), base.len(), base[0].len()).maybe_relaxed(relaxed)
        matrix = choose(base, active)
        matrix = choose(matrix, matrix.transpose())
        matrix = matrix[slice_index:slice_index].col_slice(slice_index, slice_index)
        return ret_val == call_dissolve_matrix_selection_two_args(
            matrix, matrix, opacity, rand_cons, dissolve_select_two_args_fn_obj
        )

    inv0_grammar = InvGrammar(inv0_grammar_fn, [])
    inv1_grammar = InvGrammar(inv1_grammar_fn, ["row", "agg.result"])
    return inv0_grammar, inv1_grammar, ps_grammar_fn, target_lang, fns_synths


def get_matrix_or_vec_expr_with_depth(
    matrix_or_vec_var: TensorT,
    int_var: Int,
    depth: int,
    depth_to_expr: Dict[int, Any],
    additional_matrix: Optional[Matrix[Int]] = None,
) -> TensorT:
    if depth in depth_to_expr.keys():
        return depth_to_expr[depth]
    if depth == 0:
        depth_to_expr[depth] = matrix_or_vec_var
        return matrix_or_vec_var
    expr_choices: List[Any] = []
    depth_minus_one_expr = get_matrix_or_vec_expr_with_depth(
        matrix_or_vec_var=matrix_or_vec_var,
        int_var=int_var,
        depth=depth - 1,
        depth_to_expr=depth_to_expr,
        additional_matrix=additional_matrix,
    )
    if not depth_minus_one_expr.is_matrix:
        expr_choices.append(vec_to_vec(depth_minus_one_expr))
    for other_depth in range(depth):
        other_expr = get_matrix_or_vec_expr_with_depth(
            matrix_or_vec_var=matrix_or_vec_var,
            int_var=int_var,
            depth=other_depth,
            depth_to_expr=depth_to_expr,
            additional_matrix=additional_matrix,
        )
        expr_choices.append(call_elemwise_add(depth_minus_one_expr, other_expr))
        expr_choices.append(call_elemwise_sub(depth_minus_one_expr, other_expr))
        expr_choices.append(call_elemwise_mul(depth_minus_one_expr, other_expr))
        expr_choices.append(call_elemwise_div(depth_minus_one_expr, other_expr))

        scalar = get_int_expr_with_depth(int_var, other_depth, {})
        expr_choices.append(call_scalar_add(scalar, depth_minus_one_expr))
        expr_choices.append(call_scalar_sub(scalar, depth_minus_one_expr))
        expr_choices.append(call_scalar_mul(scalar, depth_minus_one_expr))
        expr_choices.append(call_scalar_div(scalar, depth_minus_one_expr))
        expr_choices.append(call_scalar_rsub(scalar, depth_minus_one_expr))
        expr_choices.append(call_scalar_rdiv(scalar, depth_minus_one_expr))
        if additional_matrix is not None and not matrix_or_vec_var.is_matrix:
            expr_choices.append(
                call_matrix_vec_mul(additional_matrix, depth_minus_one_expr)
            )

        if other_depth != depth - 1:
            expr_choices.append(call_elemwise_sub(other_expr, depth_minus_one_expr))
            expr_choices.append(call_elemwise_div(other_expr, depth_minus_one_expr))
            scalar = get_int_expr_with_depth(int_var, depth - 1, {})
            expr_choices.append(call_scalar_add(scalar, other_expr))
            expr_choices.append(call_scalar_sub(scalar, other_expr))
            expr_choices.append(call_scalar_mul(scalar, other_expr))
            expr_choices.append(call_scalar_div(scalar, other_expr))
            expr_choices.append(call_scalar_rsub(scalar, other_expr))
            expr_choices.append(call_scalar_rdiv(scalar, other_expr))
    depth_to_expr[depth] = choose(*expr_choices)
    return depth_to_expr[depth]


def get_matrix_or_vec_expr_eq_or_below_depth(
    matrix_or_vec_var: TensorT,
    int_var: Int,
    depth: int,
    additional_matrix: Optional[Matrix[Int]] = None,
) -> Int:
    if depth >= 3:
        return get_matrix_or_vec_expr_eq_or_below_depth_with_sym_grammar(
            matrix_or_vec_var=matrix_or_vec_var,
            int_var=int_var,
            depth=depth,
            additional_matrix=additional_matrix,
        )
    depth_to_expr: Dict[int, Any] = {}
    for curr_depth in range(0, depth + 1):
        get_matrix_or_vec_expr_with_depth(
            matrix_or_vec_var=matrix_or_vec_var,
            int_var=int_var,
            depth=curr_depth,
            depth_to_expr=depth_to_expr,
            additional_matrix=additional_matrix,
        )
    final_expr = choose(*[expr for expr in depth_to_expr.values()])
    return final_expr


def get_matrix_or_vec_expr_eq_or_below_depth_with_sym_grammar(
    matrix_or_vec_var: TensorT,
    int_var: Int,
    depth: int,
    additional_matrix: Optional[Matrix[Int]] = None,
) -> Int:
    scalar = int_var
    matrix_or_vec = matrix_or_vec_var
    for _ in range(depth):
        scalar = choose(
            scalar, scalar + scalar, scalar - scalar, scalar * scalar, scalar // scalar
        )
        matrix_or_vec = choose(
            matrix_or_vec,
            call_elemwise_add(matrix_or_vec, matrix_or_vec),
            call_elemwise_sub(matrix_or_vec, matrix_or_vec),
            call_elemwise_mul(matrix_or_vec, matrix_or_vec),
            call_elemwise_div(matrix_or_vec, matrix_or_vec),
            call_scalar_add(scalar, matrix_or_vec),
            call_scalar_sub(scalar, matrix_or_vec),
            call_scalar_mul(scalar, matrix_or_vec),
            call_scalar_div(scalar, matrix_or_vec),
            call_scalar_rsub(scalar, matrix_or_vec),
            call_scalar_rdiv(scalar, matrix_or_vec),
        )
        if not matrix_or_vec.is_nested:
            matrix_or_vec = choose(matrix_or_vec, vec_to_vec(matrix_or_vec))
            if additional_matrix is not None:
                matrix_or_vec = choose(
                    call_matrix_vec_mul(additional_matrix, matrix_or_vec)
                )
    return matrix_or_vec


def get_int_expr_with_depth(
    var: Any,
    depth: int,
    depth_to_expr: Dict[int, Any],
) -> Any:
    if depth in depth_to_expr.keys():
        return depth_to_expr[depth]
    if depth == 0:
        depth_to_expr[depth] = var
        return var

    expr_choices: List[Any] = []
    depth_minus_one_expr = get_int_expr_with_depth(
        var=var,
        depth=depth - 1,
        depth_to_expr=depth_to_expr,
    )
    expr_choices.append(call_integer_sqrt(depth_minus_one_expr))
    expr_choices.append(call_integer_exp(depth_minus_one_expr))
    for other_depth in range(depth):
        other_expr = get_int_expr_with_depth(
            var=var,
            depth=other_depth,
            depth_to_expr=depth_to_expr,
        )
        expr_choices.append(depth_minus_one_expr + other_expr)
        expr_choices.append(depth_minus_one_expr - other_expr)
        expr_choices.append(depth_minus_one_expr * other_expr)
        expr_choices.append(depth_minus_one_expr // other_expr)

        # Since - and // are non-symmetric we switch the operands
        if other_depth != depth - 1:
            expr_choices.append(other_expr - depth_minus_one_expr)
            expr_choices.append(other_expr // depth_minus_one_expr)

    depth_to_expr[depth] = choose(*expr_choices)
    return depth_to_expr[depth]


def get_int_expr_eq_or_below_depth(var: Any, depth: int) -> Int:
    if depth >= 3:
        return get_int_expr_eq_or_below_depth_with_sym_grammar(var, depth)
    depth_to_expr: Dict[int, Any] = {}
    for curr_depth in range(0, depth + 1):
        get_int_expr_with_depth(
            var=var,
            depth=curr_depth,
            depth_to_expr=depth_to_expr,
        )
    final_int_expr = choose(*[int_exp for int_exp in depth_to_expr.values()])
    return final_int_expr


def get_int_expr_eq_or_below_depth_with_sym_grammar(var: Any, depth: int) -> Int:
    int_expr = var
    for _ in range(depth):
        int_expr = choose(
            int_expr,
            int_expr + int_expr,
            int_expr - int_expr,
            int_expr * int_expr,
            int_expr // int_expr,
            call_integer_exp(int_expr),
            call_integer_sqrt(int_expr),
        )
    return int_expr


def get_cond_expr_eq_or_below_depth(int_var: Int, depth: int) -> Int:
    int_expr = get_int_expr_eq_or_below_depth(var=int_var, depth=depth)
    cond_expr = choose(
        int_expr < int_expr,
        int_expr <= int_expr,
        int_expr == int_expr,
        int_expr >= int_expr,
        int_expr > int_expr,
    )
    return ite(cond_expr, int_expr, int_expr)


def get_select_synth_from_hole(
    driver: Driver, hole_body: Callable[[Int], Int]
) -> Synth:
    driver.add_var_objects([int_x, int_y])
    var = choose(int_x, int_y)
    return synth(SELECT_TWO_ARGS, hole_body(var), int_x, int_y)


def get_select_two_args_synth(select_bodies: List[Object], args: List[Object]) -> Synth:
    return synth(SELECT_TWO_ARGS, choose(*select_bodies), *args)


def get_map_int_to_int_synth(
    bodies: List[Object] = [call_integer_exp(int_x), call_integer_sqrt(int_x)]
) -> Synth:
    return synth(MAP_INT_TO_INT, choose(*bodies), int_x)


# Some **general** helper functions to get loop bounds.
outer_loop_left_bound_fn_name = "OUTER_LOOP_LEFT_BOUND"
outer_loop_right_bound_fn_name = "OUTER_LOOP_RIGHT_BOUND"


def get_lower_bound_fn_body(
    is_left_bound_smaller: Bool, left_bound: Int, right_bound: Int
) -> Int:
    return ite(
        is_left_bound_smaller,
        left_bound,
        # (for i = {var}; i > {var}; i--): right_bound + 1
        # (for i = {var}; i >= {var}; i--): right_bound
        choose(right_bound, right_bound + 1),
    )


def get_upper_bound_fn_body(
    is_left_bound_smaller: Bool, left_bound: Int, right_bound: Int
) -> Int:
    return (
        ite(
            is_left_bound_smaller,
            # (for i = {var}; i < {var}; i++): right_bound - 1
            # (for i = {var}; i <= {var}; i++): right_bound
            choose(right_bound - 1, right_bound),
            left_bound,
        )
        + 1
    )  # We add 1 here because the upper bound is exclusive


def get_loop_index_fn(
    loop_fn_args: List[Int], prefix: str = "OUTER_LOOP"
) -> Tuple[FnDecl, Synth, Callable]:
    index_fn_name = f"{prefix}_INDEX"
    index_fn_decl = fn_decl(index_fn_name, Int, None, *loop_fn_args)
    index_synth = synth(index_fn_name, choose(*loop_fn_args), *loop_fn_args)

    def get_loop_index(*args: Int) -> Int:
        return call(index_fn_name, Int, *args)

    return index_fn_decl, index_synth, get_loop_index


def get_loop_bound_fn(
    loop_fn_args: List[Int], body: Int, prefix: str = "OUTER_LOOP_LEFT"
) -> Tuple[FnDecl, Synth, Callable]:
    bound_fn_name = f"{prefix}_BOUND"
    bound_fn_decl = fn_decl(bound_fn_name, Int, None, *loop_fn_args)
    bound_synth = synth(bound_fn_name, body, *loop_fn_args)

    def get_loop_bound(*args: Int) -> Int:
        return call(bound_fn_name, Int, *args)

    return bound_fn_decl, bound_synth, get_loop_bound


def get_loop_fns(
    loop_bound_fn_args: List[Int],
    loop_index_fn_args: List[Int],
    left_bound_choices: List[Int],
    right_bound_choices: List[Int],
    prefix: str = "OUTER_LOOP",
) -> Tuple[List[FnDecl], List[Synth], Callable, Callable, Callable]:
    # TODO: add return type
    if prefix not in {"OUTER_LOOP", "INNER_LOOP"}:
        raise Exception("Prefix must be one of OUTER_LOOP and INNER_LOOP")

    index_fn_decl, index_synth, get_index = get_loop_index_fn(
        loop_index_fn_args, prefix
    )

    is_left_bound_smaller_fn_name = f"{prefix}_IS_LEFT_BOUND_SMALLER"
    (
        is_left_bound_smaller_fn_decl,
        is_left_bound_smaller_synth,
        is_left_bound_smaller,
    ) = get_no_arg_bool_fn(is_left_bound_smaller_fn_name)

    left_bound_prefix = f"{prefix}_LEFT"
    right_bound_prefix = f"{prefix}_RIGHT"
    lower_bound_prefix = f"{prefix}_LOWER"
    upper_bound_prefix = f"{prefix}_UPPER"
    left_bound_fn_decl, left_bound_synth, get_left_bound = get_loop_bound_fn(
        loop_bound_fn_args, choose(*left_bound_choices), left_bound_prefix
    )
    right_bound_fn_decl, right_bound_synth, get_right_bound = get_loop_bound_fn(
        loop_bound_fn_args, choose(*right_bound_choices), right_bound_prefix
    )
    lower_bound_fn_decl, lower_bound_synth, get_lower_bound = get_loop_bound_fn(
        loop_bound_fn_args,
        get_lower_bound_fn_body(
            is_left_bound_smaller(),
            get_left_bound(*loop_bound_fn_args),
            get_right_bound(*loop_bound_fn_args),
        ),
        lower_bound_prefix,
    )
    upper_bound_fn_decl, upper_bound_synth, get_upper_bound = get_loop_bound_fn(
        loop_bound_fn_args,
        get_upper_bound_fn_body(
            is_left_bound_smaller(),
            get_left_bound(*loop_bound_fn_args),
            get_right_bound(*loop_bound_fn_args),
        ),
        upper_bound_prefix,
    )

    all_decls = [
        index_fn_decl,
        is_left_bound_smaller_fn_decl,
        left_bound_fn_decl,
        right_bound_fn_decl,
        lower_bound_fn_decl,
        upper_bound_fn_decl,
    ]
    all_synths = [
        index_synth,
        is_left_bound_smaller_synth,
        left_bound_synth,
        right_bound_synth,
        lower_bound_synth,
        upper_bound_synth,
    ]
    return (
        all_decls,
        all_synths,
        get_lower_bound,
        get_upper_bound,
        get_index,
        is_left_bound_smaller,
    )


def get_no_arg_bool_fn(fn_name: str) -> Tuple[FnDecl, Synth, Callable]:
    bool_fn_decl = fn_decl(fn_name, Bool, None)
    bool_fn_synth = synth(fn_name, choose(Bool(True), Bool(False)))

    def call_fn() -> Bool:
        return call(fn_name, Bool)

    return bool_fn_decl, bool_fn_synth, call_fn


def get_fn_and_rv(fn_name: str, body: Any, fn_args: List[Any]) -> Any:
    decl = fn_decl(fn_name, body.type, None, *fn_args)
    fn_synth = synth(fn_name, body, *fn_args)
    rv = call(fn_name, body.type, *fn_args)
    return decl, fn_synth, rv


# list access function decls
# Define some arguments to be used
lst = mlList(Int, "lst")
matrix = Matrix(Int, "matrix")
start = Int("start")
end = Int("end")
lst_length = Int("lst_length")

vec_slice_fn_decl = fn_decl(
    "vec_slice", mlList[Int], lst[:end][start:], lst, start, end
)

vec_slice_with_length_fn_decl = fn_decl(
    "vec_slice_with_length",
    mlList[Int],
    lst[start : start + lst_length],
    lst,
    start,
    lst_length,
)

# matrix_row_slice
matrix_row_slice_fn_decl = fn_decl(
    "matrix_row_slice", Matrix[Int], matrix[:end][start:], matrix, start, end
)

# matrix_row_slice_with_length
matrix_row_slice_with_length_fn_decl = fn_decl(
    "matrix_row_slice_with_length",
    Matrix[Int],
    matrix[start : start + lst_length],
    matrix,
    start,
    lst_length,
)

# matrix_col_slice
matrix_col_slice_body = ite(
    matrix.len() < 1,
    Matrix.empty(Int),
    matrix[1:].col_slice(start, end).prepend(matrix[0][start:end]),
)
matrix_col_slice_fn_decl = fn_decl_recursive(
    "matrix_col_slice", Matrix[Int], matrix_col_slice_body, matrix, start, end
)
# matrix_col_slice_with_length
matrix_col_slice_with_length_fn_decl = fn_decl_recursive(
    "matrix_col_slice_with_length",
    Matrix[Int],
    matrix.col_slice(start, start + lst_length),
    matrix,
    start,
    lst_length,
)
# matrix transpose
firsts_body = ite(
    matrix.len() < 1,
    mlList.empty(Int),
    call("firsts", mlList[Int], matrix[1:]).prepend(matrix[0][0]),
)
firsts_fn_decl = fn_decl_recursive("firsts", mlList[Int], firsts_body, matrix)
rests_body = ite(
    matrix.len() < 1, Matrix.empty(Int), matrix.col_slice(1, matrix[0].len())
)
rests_fn_decl = fn_decl_recursive("rests", Matrix[Int], rests_body, matrix)
matrix_transpose_body = ite(
    matrix.len() < 1,
    Matrix.empty(Int),
    call("rests", Matrix[Int], matrix)
    .transpose()
    .prepend(call("firsts", mlList[Int], matrix)),
)
matrix_transpose_fn_decl = fn_decl_recursive(
    "matrix_transpose", Matrix[Int], matrix_transpose_body, matrix
)
