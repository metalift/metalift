import copy
import typing
from typing import Any, Callable, Dict, List, Optional, Tuple, Union

from pyparsing import Set

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, Fn, FnDecl, FnDeclRecursive, Int, ObjectWrapper, is_matrix_type, synth
from metalift.ir import List as mlList
from metalift.ir import (Matrix, Object, Synth, call, call_value, choose,
                         fn_decl, fn_decl_recursive, get_list_element_type,
                         get_object_exprs, is_list_type,
                         is_primitive_type, ite)
from metalift.vc_util import and_objects, or_objects
from itertools import product, combinations_with_replacement
from sympy.core.expr import Expr as symExpr
from sympy import Symbol
from sympy import Integer as symInt
from functools import lru_cache
from collections import OrderedDict

# Reduce functions
REDUCESUM = "reduce_sum"
REDUCEMUL = "reduce_mul"
REDUCEMAX = "reduce_max"

# Elemwise functions
VEC_ELEMWISE_ADD = "vec_elemwise_add"
MATRIX_ELEMWISE_ADD = "matrix_elemwise_add"
VEC_ELEMWISE_SUB = "vec_elemwise_sub"
MATRIX_ELEMWISE_SUB = "matrix_elemwise_sub"
VEC_ELEMWISE_MUL = "vec_elemwise_mul"
MATRIX_ELEMWISE_MUL = "matrix_elemwise_mul"
VEC_ELEMWISE_DIV = "vec_elemwise_div"
MATRIX_ELEMWISE_DIV = "matrix_elemwise_div"

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
SELECT_TWO_ARGS_ARG = "select_two_args_arg"
FIXED_SELECT_TWO_ARGS = "fixed_select_two_args"
SELECTION_TWO_ARGS = "selection_two_args"
MATRIX_SELECTION_TWO_ARGS = "matrix_selection_two_args"

# Uninterpreted functions
MAP_INT_TO_INT = "map_int_to_int"
# Integer functions
INTEGER_EXP = "integer_exp"
INTEGER_SQRT = "integer_sqrt"

# Operations that involve uninterpreted functions
VEC_MAP = "vec_map"
VEC_MAP_TEST_EXP = "vec_map_test_exp"
VEC_MAP_TEST_SQRT = "vec_map_test_sqrt"
MATRIX_MAP_TEST_EXP_FN_NAME = "matrix_list_map_exp"

# Other helper functions
MATRIX_VEC_MUL = "matrix_vec_mul"

MatrixOrVecT = Union[mlList[Int], Matrix[Int]]

def call_elemwise_add(left: MatrixOrVecT, right: MatrixOrVecT) -> MatrixOrVecT:
    if is_matrix_type(left.type):
        return call_matrix_elemwise_add(left, right)
    else:
        return call_vec_elemwise_add(left, right)

def call_elemwise_sub(left: MatrixOrVecT, right: MatrixOrVecT) -> MatrixOrVecT:
    if is_matrix_type(left.type):
        return call_matrix_elemwise_sub(left, right)
    else:
        return call_vec_elemwise_sub(left, right)

def call_elemwise_mul(left: MatrixOrVecT, right: MatrixOrVecT) -> MatrixOrVecT:
    if is_matrix_type(left.type):
        return call_matrix_elemwise_mul(left, right)
    else:
        return call_vec_elemwise_mul(left, right)

def call_elemwise_div(left: MatrixOrVecT, right: MatrixOrVecT) -> MatrixOrVecT:
    if is_matrix_type(left.type):
        return call_matrix_elemwise_div(left, right)
    else:
        return call_vec_elemwise_div(left, right)

def call_scalar_add(scalar: Int, matrix_or_vec: MatrixOrVecT) -> MatrixOrVecT:
    if is_matrix_type(matrix_or_vec.type):
        return call_matrix_scalar_add(scalar, matrix_or_vec)
    else:
        return call_vec_scalar_add(scalar, matrix_or_vec)

def call_scalar_sub(scalar: Int, matrix_or_vec: MatrixOrVecT) -> MatrixOrVecT:
    if is_matrix_type(matrix_or_vec.type):
        return call_matrix_scalar_sub(scalar, matrix_or_vec)
    else:
        return call_vec_scalar_sub(scalar, matrix_or_vec)

def call_scalar_mul(scalar: Int, matrix_or_vec: MatrixOrVecT) -> MatrixOrVecT:
    if is_matrix_type(matrix_or_vec.type):
        return call_matrix_scalar_mul(scalar, matrix_or_vec)
    else:
        return call_vec_scalar_mul(scalar, matrix_or_vec)

def call_scalar_div(scalar: Int, matrix_or_vec: MatrixOrVecT) -> MatrixOrVecT:
    if is_matrix_type(matrix_or_vec.type):
        return call_matrix_scalar_div(scalar, matrix_or_vec)
    else:
        return call_vec_scalar_div(scalar, matrix_or_vec)

def call_scalar_rsub(scalar: Int, matrix_or_vec: MatrixOrVecT) -> MatrixOrVecT:
    if is_matrix_type(matrix_or_vec.type):
        return call_scalar_matrix_sub(scalar, matrix_or_vec)
    else:
        return call_scalar_vec_sub(scalar, matrix_or_vec)

def call_scalar_rdiv(scalar: Int, matrix_or_vec: MatrixOrVecT) -> MatrixOrVecT:
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

def call_reduce_sum(lst) -> Int:
    return call(REDUCESUM, Int, lst)

def call_reduce_mul(lst) -> Int:
    return call(REDUCEMUL, Int, lst)

def call_reduce_max(lst) -> Int:
    return call(REDUCEMAX, Int, lst)

def call_selection(
    left: mlList[Int],
    right: mlList[Int],
    select_fn: Fn[typing.Tuple[Int, Int, Int]]
) -> mlList[Int]:
    return call(SELECTION, mlList[Int], left, right, select_fn)

def call_matrix_selection_two_args(
    left: Matrix[Int],
    right: Matrix[Int],
    select_fn: Fn[typing.Tuple[Int, Int, Int]]
) -> Matrix[Int]:
    return call(MATRIX_SELECTION_TWO_ARGS, Matrix[Int], left, right, select_fn)

def call_integer_exp(x: Int) -> Int:
    return call(INTEGER_EXP, Int, x)

def call_integer_sqrt(x: Int) -> Int:
    return call(INTEGER_SQRT, Int, x)

def call_map_int_to_int(x: Int) -> Int:
    return call(MAP_INT_TO_INT, Int, x)

def call_vec_map(x: mlList[Int], map_fn: Fn[typing.Tuple[Int, Int]]) -> mlList[Int]:
    return call(VEC_MAP, mlList[Int], x, map_fn)

def call_vec_map_exp(x: mlList[Int]) -> mlList[Int]:
    return call(VEC_MAP_TEST_EXP, mlList[Int], x)

def call_matrix_map_exp(x: Matrix[Int]) -> Matrix[Int]:
    return call(MATRIX_MAP_TEST_EXP_FN_NAME, Matrix[Int], x)

def call_uninterp_div(x: Int, y: Int) -> Int:
    return call(UNINTERP_DIV, Int, x, y)

def call_matrix_vec_mul(matrix: Matrix[Int], vec: mlList[Int]) -> mlList[Int]:
    return call(MATRIX_VEC_MUL, mlList[Int], matrix, vec)

vec_vec_to_vec = lambda left, right: choose(
    call_vec_elemwise_add(left, right),
    call_vec_elemwise_sub(left, right),
    call_vec_elemwise_mul(left, right),
    call_vec_elemwise_div(left, right)
)
scalar_vec_to_vec = lambda num, vec: choose(
    call_vec_scalar_add(num, vec),
    call_vec_scalar_sub(num, vec),
    call_vec_scalar_mul(num, vec),
    call_vec_scalar_div(num, vec),
    call_scalar_vec_sub(num, vec),
    call_scalar_vec_div(num, vec)
)
vec_to_int = lambda vec: choose(
    call_reduce_sum(vec),
    call_reduce_mul(vec),
    call_reduce_max(vec)
)
vec_to_vec = lambda vec: choose(
    call_vec_map(vec, map_int_to_int_fn_obj)
)
matrix_vec_to_vec = lambda matrix, vec: choose(
    call_matrix_vec_mul(matrix, vec)
)
matrix_to_matrix = lambda matrix: choose(
    call_matrix_transpose(matrix)
)

def vec_computation(
    args: List[mlList[Int]],
    constants: List[Int],
    compute_ops: List[str],
    depth: int
) -> mlList[Int]:
    op_to_scalar_call_mapping = {
        "+": call_vec_scalar_add,
        "-": call_vec_scalar_sub,
        "*": call_vec_scalar_mul,
        "//": call_vec_scalar_div,
    }
    op_to_elemwise_call_mapping = {
        "+": call_vec_elemwise_add,
        "-": call_vec_elemwise_sub,
        "*": call_vec_elemwise_mul,
        "//": call_vec_elemwise_div,
    }
    vec = choose(*args)
    cons = None
    if len(constants) > 0:
        cons = choose(*constants)
    for _ in range(depth):
        choices = [vec]
        for op in compute_ops:
            if cons is not None:
                choices.append(op_to_scalar_call_mapping[op](cons, vec))
            choices.append(op_to_elemwise_call_mapping[op](vec, vec))
        vec = choose(*choices)
    return vec

def matrix_computation(
    args: List[Matrix[Int]],
    constants: List[Int],
    compute_ops: List[str],
    depth: int
) -> Matrix[Int]:
    op_to_scalar_call_mapping = {
        "+": call_matrix_scalar_add,
        "-": call_matrix_scalar_sub,
        "*": call_matrix_scalar_mul,
        "//": call_matrix_scalar_div,
    }
    op_to_elemwise_call_mapping = {
        "+": call_matrix_elemwise_add,
        "-": call_matrix_elemwise_sub,
        "*": call_matrix_elemwise_mul,
        "//": call_matrix_elemwise_div,
    }
    matrix = choose(*args)
    cons = None
    if len(constants) > 0:
        cons = choose(*constants)
    for _ in range(depth):
        choices = [matrix]
        for op in compute_ops:
            if cons is not None:
                choices.append(op_to_scalar_call_mapping[op](cons, matrix))
            choices.append(op_to_elemwise_call_mapping[op](matrix, matrix))
        matrix = choose(*choices)
    return matrix

def computation_with_counts(
    args: List[Union[Matrix[Int], mlList[Int]]],
    constants: List[Int],
    ordered_compute_ops: OrderedDict,
    depth: int,
    get_constant: bool = False,
    is_vec: bool = False
) -> Optional[Union[Matrix[Int], mlList[Int], Int]]:
    if is_vec:
        op_to_scalar_call_mapping = {
            "+": call_vec_scalar_add,
            "-": call_vec_scalar_sub,
            "*": call_vec_scalar_mul,
            "//": call_vec_scalar_div,
        }
        op_to_elemwise_call_mapping = {
            "+": call_vec_elemwise_add,
            "-": call_vec_elemwise_sub,
            "*": call_vec_elemwise_mul,
            "//": call_vec_elemwise_div,
        }
    else:
        op_to_scalar_call_mapping = {
            "+": call_matrix_scalar_add,
            "-": call_matrix_scalar_sub,
            "*": call_matrix_scalar_mul,
            "//": call_matrix_scalar_div,
        }
        op_to_elemwise_call_mapping = {
            "+": call_matrix_elemwise_add,
            "-": call_matrix_elemwise_sub,
            "*": call_matrix_elemwise_mul,
            "//": call_matrix_elemwise_div,
        }
    if depth == 0:
        if get_constant:
            if len(constants) == 0:
                return None
            return choose(*constants)
        else:
            return choose(*args)
    if get_constant:
        return None
    if all(count == 0 for count in ordered_compute_ops.values()):
        return None

    # First fix left hand side to be depth - 1
    choices: Set[ObjectWrapper] = set()
    one_side_depth = depth - 1

    symmetric_ops = ["+", "*"]
    asymmetric_ops = ["-", "//"]

    one_side_depth = depth - 1
    # The other depth can be anywhere from 0 to depth - 1
    for other_side_depth in range(depth):
        for op in symmetric_ops + asymmetric_ops:
            if (op_count := ordered_compute_ops.get(op, 0)) == 0:
                continue
            visited_scalar_call_combs: Set[Tuple[int]] = set()
            visited_elemwise_call_combs: Set[Tuple[Tuple[int], Tuple[int]]] = set()
            ordered_compute_ops_copy = copy.deepcopy(ordered_compute_ops)
            ordered_compute_ops_copy[op] = op_count - 1
            ranges = [range(0, count + 1) for count in ordered_compute_ops_copy.values()]
            all_combs = set(product(*ranges))
            for comb in all_combs:
                comp_comb = get_complement_tuple(
                    tuple(ordered_compute_ops_copy.values()),
                    comb
                )
                ordered_ops = tuple(ordered_compute_ops.keys())
                compute_ops_from_comb = make_dict(ordered_ops, comb)
                compute_ops_from_comp_comb = make_dict(ordered_ops, comp_comb)
                one_side_cons = computation_with_counts(
                    args,
                    constants,
                    compute_ops_from_comb,
                    one_side_depth,
                    get_constant=True,
                    is_vec=is_vec
                )
                one_side_matrix = computation_with_counts(
                    args,
                    constants,
                    compute_ops_from_comb,
                    one_side_depth,
                    get_constant=False,
                    is_vec=is_vec
                )
                other_side_cons = computation_with_counts(
                    args,
                    constants,
                    compute_ops_from_comp_comb,
                    other_side_depth,
                    get_constant=True,
                    is_vec=is_vec
                )
                other_side_matrix = computation_with_counts(
                    args,
                    constants,
                    compute_ops_from_comp_comb,
                    other_side_depth,
                    get_constant=False,
                    is_vec=is_vec
                )
                pairs_with_scalar = [
                    (one_side_cons, other_side_matrix, comp_comb),
                    (other_side_cons, one_side_matrix, comb)
                ]
                # Handle scalar functions
                for scalar, matrix, comb in pairs_with_scalar:
                    if scalar is None or matrix is None:
                        continue
                    if comb in visited_scalar_call_combs:
                        continue
                    call_result = ObjectWrapper(op_to_scalar_call_mapping[op](scalar, matrix))
                    choices.add(call_result)
                    visited_scalar_call_combs.add(comb)

                # Handle elemwise functions
                if one_side_matrix is None or other_side_matrix is None:
                    continue
                elemwise_call = op_to_elemwise_call_mapping[op]
                if op in symmetric_ops:
                    if (comb, comp_comb) not in visited_elemwise_call_combs:
                        call_result = elemwise_call(one_side_matrix, other_side_matrix)
                        choices.add(ObjectWrapper(call_result))
                        visited_elemwise_call_combs.add((comb, comp_comb))
                        visited_elemwise_call_combs.add((comp_comb, comb))
                elif op in asymmetric_ops:
                    if (comb, comp_comb) not in visited_elemwise_call_combs:
                        call_result = elemwise_call(one_side_matrix, other_side_matrix)
                        choices.add(ObjectWrapper(call_result))
                        visited_elemwise_call_combs.add((comb, comp_comb))
                    if (comp_comb, comb) not in visited_elemwise_call_combs:
                        call_result = elemwise_call(other_side_matrix, one_side_matrix)
                        choices.add(ObjectWrapper(call_result))
                        visited_elemwise_call_combs.add((comp_comb, comb))


    if len(choices) == 0:
        return None
    return choose(*[choice.object for choice in choices])


# Define some common objects
a = Int("a")
x = mlList(Int, "x")
y = mlList(Int, "y")
matrix_x = Matrix(Int, "matrix_x")
matrix_y = Matrix(Int, "matrix_y")
int_x = Int("int_x")
int_y = Int("int_y")

def vector_add_body(left: mlList[Int], right: mlList[Int]) -> mlList[Int]:
    vec_size = left.len()
    cur = left[0] + right[0]
    left_rest = left[1:]
    right_rest = right[1:]
    recursed = call_vector_add(left_rest, right_rest)
    general_answer = recursed.prepend(cur)
    return ite(vec_size < 1, mlList.empty(Int), general_answer)
vector_add = fn_decl_recursive(VECTORADD, mlList[Int], vector_add_body(x, y), x, y)

def scalar_mul_body(scalar: Int, arr: mlList[Int]) -> mlList[Int]:
    vec_size = arr.len()
    cur = scalar * arr[0]
    arr_rest = arr[1:]
    recursed = call_scalar_mul(scalar, arr_rest)
    general_answer = recursed.prepend(cur)
    return ite(vec_size < 1, mlList.empty(Int), general_answer)
scalar_mul = fn_decl_recursive(SCALARMUL, mlList[Int], scalar_mul_body(a, x), a, x)

def broadcast_add_body(scalar: Int, arr: mlList[Int]) -> mlList[Int]:
    vec_size = arr.len()
    cur = scalar + arr[0]
    arr_rest = arr[1:]
    recursed = call_broadcast_add(scalar, arr_rest)
    general_answer = recursed.prepend(cur)
    return ite(vec_size < 1, mlList.empty(Int), general_answer)
broadcast_add = fn_decl_recursive(BROADCASTADD, mlList[Int], broadcast_add_body(a, x), a, x)

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
    return ite(vec_size <= 1, lst[0], general_answer)
reduce_max = fn_decl_recursive(REDUCEMAX, Int, reduce_max_body(x), x)

def matrix_vec_mul_body(matrix: Matrix[Int], vec: mlList[Int]) -> mlList[Int]:
    invalid_cond = or_objects(
        matrix.len() < 1,
        matrix[0].len() < 1,
        matrix[0].len() != vec.len()
    )
    cur = call_reduce_sum(call_vec_elemwise_mul(matrix[0], vec))
    recursed = call_matrix_vec_mul(matrix[1:], vec)
    return ite(invalid_cond, mlList.empty(Int), recursed.prepend(cur))
matrix_vec_mul = fn_decl_recursive(MATRIX_VEC_MUL, mlList[Int], matrix_vec_mul_body(matrix_x, x), matrix_x, x)

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

def matrix_mul8x8_div32_body(nested_x: Matrix[Int], nested_y: Matrix[Int]) -> Matrix[Int]:
    return call_matrix_scalar_div(
        Int(32),
        call_matrix_elemwise_mul(nested_x, nested_y)
    )

def vec_screen8x8_body(x: mlList[Int], y: mlList[Int]) -> mlList[Int]:
    return call_vec_elemwise_sub(
        call_vec_elemwise_add(x, y),
        vec_mul8x8_div32_body(x, y)
    )

def matrix_screen8x8_body(nested_x: Matrix[Int], nested_y: Matrix[Int]) -> Matrix[Int]:
    return call_matrix_elemwise_sub(
        call_matrix_elemwise_add(nested_x, nested_y),
        matrix_mul8x8_div32_body(nested_x, nested_y)
    )

def vec_linear_burn_body(x: mlList[Int], y: mlList[Int]) -> mlList[Int]:
    return call_vec_scalar_sub(
        Int(32),
        call_vec_elemwise_add(x, y),
    )

def matrix_linear_burn_body(nested_x: Matrix[Int], nested_y: Matrix[Int]) -> Matrix[Int]:
    return call_matrix_scalar_sub(
        Int(32),
        call_matrix_elemwise_add(nested_x, nested_y)
    )

# Helper functions for compute benchmarks using the holing approach
def multiply_blend_8_hole_body(matrix_or_vec: MatrixOrVecT) -> MatrixOrVecT:
    cons = choose(Int(32))
    return call_scalar_div(
        cons,
        call_elemwise_mul(matrix_or_vec, matrix_or_vec)
    )

def linear_burn_8_hole_body(matrix_or_vec: MatrixOrVecT) -> MatrixOrVecT:
    cons = choose(Int(32))
    return call_scalar_sub(
        cons,
        call_elemwise_add(matrix_or_vec, matrix_or_vec)
    )


def screen_blend_8_hole_body(matrix_or_vec: MatrixOrVecT) -> MatrixOrVecT:
    cons = choose(Int(32))
    return call_elemwise_sub(
        call_elemwise_add(matrix_or_vec, matrix_or_vec),
        call_scalar_div(
            cons,
            call_elemwise_mul(matrix_or_vec, matrix_or_vec)
        )
    )

def linear_dodge_8_hole_body(matrix_or_vec: MatrixOrVecT) -> MatrixOrVecT:
    return call_elemwise_add(matrix_or_vec, matrix_or_vec)

# Helper functions for select benchmarks using the holing approach
def darken_blend_8_hole_body(int_var: Int) -> Int:
    return ite(
        int_var > int_var,
        int_var,
        int_var
    )

def color_burn_8_hole_body(int_var: Int) -> Int:
    cons = choose(Int(0), Int(32))
    return ite(
        int_var == cons,
        cons,
        cons - (cons - int_var) // int_var
    )

def lighten_blend_8_hole_body(int_var: Int) -> Int:
    return ite(
        int_var < int_var,
        int_var,
        int_var
    )

def color_dodge_8_hole_body(int_var: Int) -> Int:
    cons = choose(Int(32))
    return ite(
        int_var == cons,
        cons,
        int_var // (cons - int_var)
    )

def overlay_blend_8_hole_body(int_var: Int) -> Int:
    cons = choose(Int(2), Int(16), Int(32))
    return ite(
        int_var >= cons,
        cons * int_var + int_var - cons * int_var * int_var // cons - cons,
        cons * int_var * int_var // cons
    )

# Selection criteria
def select_darken_blend_body(int_x: IntObject, int_y: IntObject) -> IntObject:
    return ite(int_x > int_y, int_y, int_x)

def select_color_burn_body(int_x: Int, int_y: Int) -> Int:
    return ite(
        int_y == 0,
        Int(32),
        32 - (32 - int_x) // int_y
    )

def select_lighten_blend_body(int_x: Int, int_y: Int) -> Int:
    return ite(int_x < int_y, int_y, int_x)

def select_color_dodge_body(int_x: Int, int_y: Int) -> Int:
    return ite(
        int_y == 32,
        Int(32),
        int_x // (32 - int_y)
    )

def select_overlay_blend_body(int_x: Int, int_y: Int) -> Int:
    return ite(
        int_x >= 16,
        screen8x8_body(2 * int_x, int_x) - 32,
        mul8x8_div32_body(2 * int_x, int_x)
    )

select_two_args_fn_obj_arg = Fn((Int, Int, Int), SELECT_TWO_ARGS_ARG)
select_two_args_fn_obj = Fn((Int, Int, Int), SELECT_TWO_ARGS)
fixed_select_two_args_fn_obj = Fn((Int, Int, Int), FIXED_SELECT_TWO_ARGS)
select_two_args_fn_decl = fn_decl(SELECT_TWO_ARGS, Int, None, int_x, int_y)
fixed_select_two_args_fn_decl = fn_decl(
    FIXED_SELECT_TWO_ARGS,
    Int,
    None,
    int_x,
    int_y
)
map_int_to_int_fn_obj = Fn((Int, Int), MAP_INT_TO_INT)
map_int_to_int = fn_decl(
    MAP_INT_TO_INT,
    Int,
    None,
    int_x
)

def matrix_selection_two_args_body(
    left: Matrix[Int],
    right: Matrix[Int],
    select_fn: Fn[typing.Tuple[Int, Int, Int]]
) -> Matrix[Int]:
    cur = call_selection_two_args(left[0], right[0], select_fn)
    recursed = call_matrix_selection_two_args(left[1:], right[1:], select_fn)
    general_answer = recursed.prepend(cur)
    return ite(
        or_objects(left.len() < 1, left.len() != right.len()),
        Matrix.empty(Int),
        general_answer
    )
matrix_selection_two_args_fn_decl = fn_decl_recursive(
    MATRIX_SELECTION_TWO_ARGS,
    Matrix[Int],
    matrix_selection_two_args_body(matrix_x, matrix_y, select_two_args_fn_obj_arg),
    matrix_x,
    matrix_y,
    select_two_args_fn_obj_arg
)

def selection_two_args_body(
    left: mlList[Int],
    right: mlList[Int],
    select_fn: Fn[typing.Tuple[Int, Int, Int]]
) -> mlList[Int]:
    cur = call_value(select_fn, left[0], right[0])
    recursed = call_selection_two_args(left[1:], right[1:], select_fn)
    general_answer = recursed.prepend(cur)
    return ite(
        or_objects(left.len() < 1, left.len() != right.len()),
        mlList.empty(Int),
        general_answer
    )
selection_two_args_fn_decl = fn_decl_recursive(
    SELECTION_TWO_ARGS,
    mlList[Int],
    selection_two_args_body(x, y, select_two_args_fn_obj_arg),
    x,
    y,
    select_two_args_fn_obj_arg
)


def selection_two_args_ps_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    ret_val = writes[0]
    base, active = reads
    # return ret_val == call_nested_selection_two_args(base, active, fixed_select_two_args_fn_obj)
    base_or_active = choose(base, active)
    return ret_val == call_matrix_selection_two_args(base_or_active, base_or_active, select_two_args_fn_obj)

def selection_two_args_inv0_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    # outer loop grammar
    writes_by_name = {
        w.var_name(): w
        for w in writes
    }
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
        out == call_matrix_selection_two_args(matrix, matrix, select_two_args_fn_obj)
    )

def selection_two_args_inv1_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    # inner loop grammar
    writes_by_name = {
        w.var_name(): w
        for w in writes
    }
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
    matrix = choose(
        base[:row],
        base[:col],
        active[:row],
        active[:col]
    )
    return and_objects(
        row >= index_lower_bound,
        row < index_upper_bound,
        col >= index_lower_bound,
        col <= index_upper_bound,
        row_vec == call_selection_two_args(vec, vec, select_two_args_fn_obj),
        out == call_matrix_selection_two_args(matrix, matrix, select_two_args_fn_obj)
    )

def selection_two_args_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        select_two_args_fn_decl,
        # fixed_select_two_args_fn_decl,
        selection_two_args_fn_decl,
        matrix_selection_two_args_fn_decl
    ]

selection_two_args_inv0_grammar = InvGrammar(selection_two_args_inv0_grammar_fn, [])
selection_two_args_inv1_grammar = InvGrammar(selection_two_args_inv1_grammar_fn, ["row", "agg.result"])

def elemwise_body(
    left: Union[mlList[Int], Matrix[Int]],
    right: Union[mlList[Int], Matrix[Int]],
    compute_fn: Callable[[Int, Int], Int],
    vec_fn_name: str,
    matrix_fn_name: str
) -> Union[mlList[Int], Matrix[Int]]:
    if is_matrix_type(left.type) and is_matrix_type(right.type):
        cur = call(vec_fn_name, mlList[Int], left[0], right[0])
        recursed = call(matrix_fn_name, Matrix[Int], left[1:], right[1:])
        general_answer = recursed.prepend(cur)
        return ite(
            or_objects(left.len() < 1, left.len() != right.len()),
            Matrix.empty(Int),
            general_answer
        )
    elif is_list_type(left.type) and is_primitive_type(get_list_element_type(left.type)) and is_list_type(right.type) and is_primitive_type(get_list_element_type(right.type)):
        cur = compute_fn(left[0], right[0])
        recursed = call(vec_fn_name, mlList[Int], left[1:], right[1:])
        general_answer = recursed.prepend(cur)
        return ite(
            or_objects(left.len() < 1, left.len() != right.len()),
            mlList.empty(Int),
            general_answer
        )
    raise Exception("Unsupported types for elemwise operations!")

def scalar_body(
    scalar: Int,
    vec_or_matrix: Union[mlList[Int], Matrix[Int]],
    compute_fn: Callable[[Int, Int], Int],
    vec_fn_name: str,
    matrix_fn_name: str
) -> Union[mlList[Int], Matrix[Int]]:
    if is_matrix_type(vec_or_matrix.type):
        cur = call(vec_fn_name, mlList[Int], scalar, vec_or_matrix[0])
        recursed = call(matrix_fn_name, Matrix[Int], scalar, vec_or_matrix[1:])
        general_answer = recursed.prepend(cur)
        return ite(
            or_objects(vec_or_matrix.len() < 1),
            Matrix.empty(Int),
            general_answer
        )
    elif is_list_type(vec_or_matrix.type) and is_primitive_type(get_list_element_type(vec_or_matrix.type)):
        cur = compute_fn(scalar, vec_or_matrix[0])
        recursed = call(vec_fn_name, mlList[Int], scalar, vec_or_matrix[1:])
        general_answer = recursed.prepend(cur)
        return ite(
            or_objects(vec_or_matrix.len() < 1),
            mlList.empty(Int),
            general_answer
        )
    raise Exception("Unsupported types for scalar operations!")

def map_body(
    vec_or_matrix: Union[mlList[Int], Matrix[Int]],
    map_fn: Callable[[Int], Int],
    vec_map_fn_name: str,
    matrix_map_fn_name: str
) -> Union[mlList[Int], Matrix[Int]]:
    if is_matrix_type(vec_or_matrix.type):
        cur = call(vec_map_fn_name, mlList[Int], vec_or_matrix[0])
        recursed = call(matrix_map_fn_name, Matrix[Int], vec_or_matrix[1:])
        general_answer = recursed.prepend(cur)
        return ite(
            or_objects(vec_or_matrix.len() < 1),
            Matrix.empty(Int),
            general_answer
        )
    elif is_list_type(vec_or_matrix.type) and is_primitive_type(get_list_element_type(vec_or_matrix.type)):
        cur = map_fn(vec_or_matrix[0])
        recursed = call(vec_map_fn_name, mlList[Int], vec_or_matrix[1:])
        general_answer = recursed.prepend(cur)
        return ite(
            or_objects(vec_or_matrix.len() < 1),
            mlList.empty(Int),
            general_answer
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
        matrix_fn_name=MATRIX_ELEMWISE_ADD
    ),
    x,
    y
)
matrix_elemwise_add = fn_decl_recursive(
    MATRIX_ELEMWISE_ADD,
    Matrix[Int],
    elemwise_body(
        left=matrix_x,
        right=matrix_y,
        compute_fn=lambda int_x, int_y: int_x + int_y,
        vec_fn_name=VEC_ELEMWISE_ADD,
        matrix_fn_name=MATRIX_ELEMWISE_ADD
    ),
    matrix_x,
    matrix_y
)

vec_elemwise_sub = fn_decl_recursive(
    VEC_ELEMWISE_SUB,
    mlList[Int],
    elemwise_body(
        left=x,
        right=y,
        compute_fn=lambda int_x, int_y: int_x - int_y,
        vec_fn_name=VEC_ELEMWISE_SUB,
        matrix_fn_name=MATRIX_ELEMWISE_SUB
    ),
    x,
    y
)
matrix_elemwise_sub = fn_decl_recursive(
    MATRIX_ELEMWISE_SUB,
    Matrix[Int],
    elemwise_body(
        left=matrix_x,
        right=matrix_y,
        compute_fn=lambda int_x, int_y: int_x + int_y,
        vec_fn_name=VEC_ELEMWISE_SUB,
        matrix_fn_name=MATRIX_ELEMWISE_SUB
    ),
    matrix_x,
    matrix_y
)

vec_elemwise_mul = fn_decl_recursive(
    VEC_ELEMWISE_MUL,
    mlList[Int],
    elemwise_body(
        left=x,
        right=y,
        compute_fn=lambda int_x, int_y: int_x * int_y,
        vec_fn_name=VEC_ELEMWISE_MUL,
        matrix_fn_name=MATRIX_ELEMWISE_MUL
    ),
    x,
    y
)
matrix_elemwise_mul = fn_decl_recursive(
    MATRIX_ELEMWISE_MUL,
    Matrix[Int],
    elemwise_body(
        left=matrix_x,
        right=matrix_y,
        compute_fn=lambda int_x, int_y: int_x * int_y,
        vec_fn_name=VEC_ELEMWISE_MUL,
        matrix_fn_name=MATRIX_ELEMWISE_MUL
    ),
    matrix_x,
    matrix_y
)

vec_elemwise_div = fn_decl_recursive(
    VEC_ELEMWISE_DIV,
    mlList[Int],
    elemwise_body(
        left=x,
        right=y,
        compute_fn=lambda int_x, int_y: int_x // int_y,
        vec_fn_name=VEC_ELEMWISE_DIV,
        matrix_fn_name=MATRIX_ELEMWISE_DIV
    ),
    x,
    y
)
matrix_elemwise_div = fn_decl_recursive(
    MATRIX_ELEMWISE_DIV,
    Matrix[Int],
    elemwise_body(
        left=matrix_x,
        right=matrix_y,
        compute_fn=lambda int_x, int_y: int_x // int_y,
        vec_fn_name=VEC_ELEMWISE_DIV,
        matrix_fn_name=MATRIX_ELEMWISE_DIV
    ),
    matrix_x,
    matrix_y
)

vec_scalar_add = fn_decl_recursive(
    VEC_SCALAR_ADD,
    mlList[Int],
    scalar_body(
        scalar=a,
        vec_or_matrix=x,
        compute_fn=lambda scalar, int_x: scalar + int_x,
        vec_fn_name=VEC_SCALAR_ADD,
        matrix_fn_name=MATRIX_SCALAR_ADD
    ),
    a,
    x
)
matrix_scalar_add = fn_decl_recursive(
    MATRIX_SCALAR_ADD,
    mlList[Int],
    scalar_body(
        scalar=a,
        vec_or_matrix=matrix_x,
        compute_fn=lambda scalar, int_x: scalar + int_x,
        vec_fn_name=VEC_SCALAR_ADD,
        matrix_fn_name=MATRIX_SCALAR_ADD
    ),
    a,
    matrix_x
)

vec_scalar_mul = fn_decl_recursive(
    VEC_SCALAR_MUL,
    mlList[Int],
    scalar_body(
        scalar=a,
        vec_or_matrix=x,
        compute_fn=lambda scalar, int_x: scalar * int_x,
        vec_fn_name=VEC_SCALAR_MUL,
        matrix_fn_name=MATRIX_SCALAR_MUL
    ),
    a,
    x
)
matrix_scalar_mul = fn_decl_recursive(
    MATRIX_SCALAR_MUL,
    mlList[Int],
    scalar_body(
        scalar=a,
        vec_or_matrix=matrix_x,
        compute_fn=lambda scalar, int_x: scalar * int_x,
        vec_fn_name=VEC_SCALAR_MUL,
        matrix_fn_name=MATRIX_SCALAR_MUL
    ),
    a,
    matrix_x
)

vec_scalar_div = fn_decl_recursive(
    VEC_SCALAR_DIV,
    mlList[Int],
    scalar_body(
        scalar=a,
        vec_or_matrix=x,
        compute_fn=lambda scalar, int_x: int_x // scalar,
        vec_fn_name=VEC_SCALAR_DIV,
        matrix_fn_name=MATRIX_SCALAR_DIV
    ),
    a,
    x
)
scalar_vec_div = fn_decl_recursive(
    SCALAR_VEC_DIV,
    mlList[Int],
    scalar_body(
        scalar=a,
        vec_or_matrix=x,
        compute_fn=lambda scalar, int_x: scalar // int_x,
        vec_fn_name=SCALAR_VEC_DIV,
        matrix_fn_name=SCALAR_MATRIX_DIV
    ),
    a,
    x
)
matrix_scalar_div = fn_decl_recursive(
    MATRIX_SCALAR_DIV,
    Matrix[Int],
    scalar_body(
        scalar=a,
        vec_or_matrix=matrix_x,
        compute_fn=lambda scalar, int_x: int_x // scalar,
        vec_fn_name=VEC_SCALAR_DIV,
        matrix_fn_name=MATRIX_SCALAR_DIV
    ),
    a,
    matrix_x
)
scalar_matrix_div = fn_decl_recursive(
    SCALAR_MATRIX_DIV,
    Matrix[Int],
    scalar_body(
        scalar=a,
        vec_or_matrix=matrix_x,
        compute_fn=lambda scalar, int_x: scalar // int_x,
        vec_fn_name=SCALAR_VEC_DIV,
        matrix_fn_name=SCALAR_MATRIX_DIV
    ),
    a,
    matrix_x
)

vec_scalar_sub = fn_decl_recursive(
    VEC_SCALAR_SUB,
    mlList[Int],
    scalar_body(
        scalar=a,
        vec_or_matrix=x,
        compute_fn=lambda scalar, int_x: int_x - scalar,
        vec_fn_name=VEC_SCALAR_SUB,
        matrix_fn_name=MATRIX_SCALAR_SUB
    ),
    a,
    x
)
scalar_vec_sub = fn_decl_recursive(
    SCALAR_VEC_SUB,
    mlList[Int],
    scalar_body(
        scalar=a,
        vec_or_matrix=x,
        compute_fn=lambda scalar, int_x: scalar - int_x,
        vec_fn_name=SCALAR_VEC_SUB,
        matrix_fn_name=SCALAR_MATRIX_SUB
    ),
    a,
    x
)
matrix_scalar_sub = fn_decl_recursive(
    MATRIX_SCALAR_SUB,
    Matrix[Int],
    scalar_body(
        scalar=a,
        vec_or_matrix=matrix_x,
        compute_fn=lambda scalar, int_x: int_x - scalar,
        vec_fn_name=VEC_SCALAR_SUB,
        matrix_fn_name=MATRIX_SCALAR_SUB
    ),
    a,
    matrix_x
)
scalar_matrix_sub = fn_decl_recursive(
    SCALAR_MATRIX_SUB,
    Matrix[Int],
    scalar_body(
        scalar=a,
        vec_or_matrix=matrix_x,
        compute_fn=lambda scalar, int_x: int_x - scalar,
        vec_fn_name=SCALAR_VEC_SUB,
        matrix_fn_name=SCALAR_MATRIX_SUB
    ),
    a,
    matrix_x
)

def vec_map_body(
    vec: mlList[Int],
    map_fn: Fn[typing.Tuple[Int, Int]]
) -> mlList[Int]:
    cur = call_value(map_fn, vec[0])
    recursed = call_vec_map(vec[1:], map_fn)
    return ite(
        vec.len() < 1,
        mlList.empty(Int),
        recursed.prepend(cur)
    )
vec_map = fn_decl_recursive(
    VEC_MAP,
    mlList[Int],
    vec_map_body(x, map_int_to_int_fn_obj),
    x,
    map_int_to_int_fn_obj
)

# Uninterpreted functions
# TODO(jie): this is returning a random prime
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
    scalar_vec_div
]
scalar_matrix_to_matrix_target_lang = [
    matrix_scalar_add,
    matrix_scalar_sub,
    matrix_scalar_mul,
    matrix_scalar_div,
    scalar_matrix_sub,
    scalar_matrix_div
]
vec_to_int_target_lang = [
    reduce_max,
    reduce_sum,
    reduce_mul
]
matrix_vec_to_vec_target_lang = [matrix_vec_mul, vec_elemwise_mul, reduce_sum]
vec_to_vec_target_lang = [vec_map, map_int_to_int]

def get_matrix_computation_ps_grammar_fn(
    fixed_grammar: bool,
    fixed_out_fn: Optional[Any] = None, # TODO(jie): add type for this
    constants: Optional[List[Int]] = None,
    compute_ops: Optional[List[str]] = None,
    depth: Optional[int] = None,
) -> Callable[[List[Object], List[Object], List[Object]], Bool]:
    if fixed_grammar:
        raise Exception("Must not fix ps grammar!")
        if fixed_out_fn is None:
            raise Exception("Must pass in an override out!")
    def matrix_computation_ps_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
        ret_val = writes[0]
        base, active = reads
        if not fixed_grammar:
            return ret_val == matrix_computation(
                args=[base, active],
                constants=constants,
                compute_ops=compute_ops,
                depth=depth
            )
        else:
            return ret_val == fixed_out_fn(base, active)
    return matrix_computation_ps_grammar_fn

def get_matrix_computation_hole_inv0_grammar(hole_body: Callable[[MatrixOrVecT], MatrixOrVecT]) -> InvGrammar:
    def inv0_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
        # outer loop grammar
        out, col, pixel, row, row_vec = writes
        base, active = reads
        index_lower_bound = choose(Int(0), Int(1))
        index_upper_bound = choose(base.len(), base[0].len(), active.len(), active[0].len())
        matrix = choose(
            base[:row],
            base[:col],
            active[:row],
            active[:col]
        )
        return and_objects(
            row >= index_lower_bound,
            row <= index_upper_bound,
            out == hole_body(matrix)
        )
    return InvGrammar(inv0_grammar_fn, [])

def get_dexter_double_loop_fns() -> Tuple[
    List[FnDecl],
    List[Synth],
    Callable,
    Callable,
    Bool,
]:
    # Get loop index functions
    row_var = Int("row")
    col_var = Int("col")
    outer_loop_index_fn_decl, outer_loop_index_synth, get_outer_loop_index = get_loop_index_fn(
        loop_fn_args=[row_var, col_var],
        prefix="OUTER_LOOP"
    )
    inner_loop_index_fn_decl, inner_loop_index_synth, get_inner_loop_index = get_loop_index_fn(
        loop_fn_args=[row_var, col_var],
        prefix="INNER_LOOP"
    )
    outer_loop_index_first_fn_name = "OUTER_LOOP_INDEX_FIRST"
    (
        outer_loop_index_first_fn_decl,
        outer_loop_index_first_synth,
        is_outer_loop_index_first
    ) = get_no_arg_bool_fn(outer_loop_index_first_fn_name)

    fn_decls = [
        outer_loop_index_fn_decl,
        inner_loop_index_fn_decl,
        outer_loop_index_first_fn_decl,
    ]
    synths = [
        outer_loop_index_synth,
        inner_loop_index_synth,
        outer_loop_index_first_synth,
    ]
    return (
        fn_decls,
        synths,
        get_outer_loop_index,
        get_inner_loop_index,
        is_outer_loop_index_first
    )

def get_matrix_computation_holing_search_space(
    hole_body: Callable[[MatrixOrVecT], MatrixOrVecT]
) -> Tuple[
    InvGrammar,
    InvGrammar,
    Callable[[List[Object], List[Object], List[Object]], List[Object]],
    Callable[[], List[Union[FnDecl, FnDeclRecursive]]],
    List[Synth]
]:
    (
        loop_fn_decls,
        loop_synths,
        get_outer_loop_index,
        get_inner_loop_index,
        is_outer_loop_index_first,
    ) = get_dexter_double_loop_fns()


    # Target language
    def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
        return [
            *loop_fn_decls,
            *scalar_vec_to_vec_target_lang,
            *scalar_matrix_to_matrix_target_lang,
            *vec_vec_to_vec_target_lang,
            *matrix_matrix_to_matrix_target_lang
        ]

    fns_synths = loop_synths

    # inv0 grammar
    def inv0_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
        out, col, pixel, row, row_vec = writes
        base, active = reads
        int_vars = [row, col]
        outer_loop_index = get_outer_loop_index(*int_vars)
        matrix = choose(base, active)
        matrix = ite(
            is_outer_loop_index_first(), # Then outer loop has to be over row
            matrix[:outer_loop_index],
            matrix.col_slice(0, outer_loop_index)
        )
        matrix = choose(matrix, matrix.transpose())
        return and_objects(
            outer_loop_index >= 0,
            outer_loop_index <= ite(
                is_outer_loop_index_first(),
                base.len(),
                base[0].len()
            ),
            out == hole_body(matrix)
        )

    def inv1_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
        col, pixel, row_vec = writes
        out, row = in_scope
        base, active = reads
        int_vars = [row, col]
        outer_loop_index = get_outer_loop_index(*int_vars)
        inner_loop_index = get_inner_loop_index(*int_vars)
        matrix = choose(base, active)
        outer_loop_matrix = ite(
            is_outer_loop_index_first(), # Then outer loop has to be over row
            matrix[:outer_loop_index],
            matrix.col_slice(0, outer_loop_index)
        )
        outer_loop_matrix = choose(outer_loop_matrix, outer_loop_matrix.transpose())
        inner_loop_vec = ite(
            is_outer_loop_index_first(),
            matrix[outer_loop_index][:inner_loop_index],
            matrix[:inner_loop_index].col_vec(outer_loop_index)
        )
        return and_objects(
            outer_loop_index >= 0,
            outer_loop_index < ite(
                is_outer_loop_index_first(),
                base.len(),
                base[0].len()
            ),
            inner_loop_index >= 0,
            inner_loop_index <= ite(
                is_outer_loop_index_first(),
                base[0].len(),
                base.len()
            ),
            row_vec == hole_body(inner_loop_vec),
            out == hole_body(outer_loop_matrix)
        )

    def ps_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
        ret_val = writes[0]
        base, active = reads
        matrix = choose(base, active)
        matrix = choose(matrix, matrix.transpose())
        return ret_val == hole_body(matrix)

    inv0_grammar = InvGrammar(inv0_grammar_fn, [])
    inv1_grammar = InvGrammar(inv1_grammar_fn, ["row", "agg.result"])
    return inv0_grammar, inv1_grammar, ps_grammar_fn, target_lang, fns_synths

def get_matrix_select_holing_search_space(
    driver: Driver,
    hole_body: Callable[[Int], Int]
) -> Tuple[
    InvGrammar,
    InvGrammar,
    Callable[[List[Object], List[Object], List[Object]], List[Object]],
    Callable[[], List[Union[FnDecl, FnDeclRecursive]]],
    List[Synth]
]:
    (
        loop_fn_decls,
        loop_synths,
        get_outer_loop_index,
        get_inner_loop_index,
        is_outer_loop_index_first
    ) = get_dexter_double_loop_fns()

    # Target language
    def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
        return [
            *loop_fn_decls,
            select_two_args_fn_decl,
            selection_two_args_fn_decl,
            matrix_selection_two_args_fn_decl
        ]

    # Functions to synthesize
    select_synth = get_select_synth_from_hole(driver, hole_body)
    fns_synths = [select_synth, *loop_synths]

    # inv0 grammar
    def inv0_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
        out, col, pixel, row, row_vec = writes
        base, active = reads
        int_vars = [row, col]
        outer_loop_index = get_outer_loop_index(*int_vars)
        matrix = choose(base, active)
        matrix = ite(
            is_outer_loop_index_first(), # Then outer loop has to be over row
            matrix[:outer_loop_index],
            matrix.col_slice(0, outer_loop_index)
        )
        matrix = choose(matrix, matrix.transpose())
        return and_objects(
            outer_loop_index >= 0,
            outer_loop_index <= ite(
                is_outer_loop_index_first(),
                base.len(),
                base[0].len()
            ),
            out == call_matrix_selection_two_args(matrix, matrix, select_two_args_fn_obj)
        )

    def inv1_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
        col, pixel, row_vec = writes
        out, row = in_scope
        base, active = reads
        int_vars = [row, col]
        outer_loop_index = get_outer_loop_index(*int_vars)
        inner_loop_index = get_inner_loop_index(*int_vars)

        matrix = choose(base, active)
        outer_loop_matrix = ite(
            is_outer_loop_index_first(), # Then outer loop has to be over row
            matrix[:outer_loop_index],
            matrix.col_slice(0, outer_loop_index)
        )
        outer_loop_matrix = choose(outer_loop_matrix, outer_loop_matrix.transpose())
        inner_loop_vec = ite(
            is_outer_loop_index_first(),
            matrix[outer_loop_index][:inner_loop_index],
            matrix[:inner_loop_index].col_vec(outer_loop_index)
        )
        return and_objects(
            outer_loop_index >= 0,
            outer_loop_index < ite(
                is_outer_loop_index_first(),
                base.len(),
                base[0].len()
            ),
            inner_loop_index >= 0,
            inner_loop_index <= ite(
                is_outer_loop_index_first(),
                base[0].len(),
                base.len()
            ),
            row_vec == call_selection_two_args(
                inner_loop_vec,
                inner_loop_vec,
                select_two_args_fn_obj
            ),
            out == call_matrix_selection_two_args(
                outer_loop_matrix,
                outer_loop_matrix,
                select_two_args_fn_obj
            )
        )

    def ps_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
        ret_val = writes[0]
        base, active = reads
        matrix = choose(base, active)
        matrix = choose(matrix, matrix.transpose())
        return ret_val == call_matrix_selection_two_args(matrix, matrix, select_two_args_fn_obj)

    inv0_grammar = InvGrammar(inv0_grammar_fn, [])
    inv1_grammar = InvGrammar(inv1_grammar_fn, ["row", "agg.result"])
    return inv0_grammar, inv1_grammar, ps_grammar_fn, target_lang, fns_synths


def get_matrix_computation_inv0_grammar(
    fixed_grammar: bool,
    fixed_out_fn: Optional[Any] = None, # TODO(jie): add type for this
    constants: Optional[List[Int]] = None,
    compute_ops: Optional[List[str]] = None,
    depth: Optional[int] = None,
) -> InvGrammar:
    if fixed_grammar:
        if fixed_out_fn is None:
            raise Exception("Must pass in an override out!")
    def matrix_computation_inv0_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
        # outer loop grammar
        out, col, pixel, row, row_vec = writes
        base, active = reads
        if not fixed_grammar:
            index_lower_bound = choose(Int(0), Int(1))
            index_upper_bound = choose(base.len(), base[0].len())
            index_lower_cond = choose(
                row >= index_lower_bound,
                row > index_lower_bound,
                row == index_lower_bound,
                row < index_lower_bound,
                row <= index_lower_bound
            )
            index_upper_cond = choose(
                row >= index_upper_bound,
                row > index_upper_bound,
                row == index_upper_bound,
                row < index_upper_bound,
                row <= index_upper_bound
            )
            matrix_choices = [
                base,
                base[:row],
                base[:col],
                active,
                active[:row],
                active[:col],
            ]
            return and_objects(
                index_lower_cond,
                index_upper_cond,
                out == matrix_computation(
                    args=matrix_choices,
                    constants=constants,
                    compute_ops=compute_ops,
                    depth=depth
                )
            )
        else:
            return and_objects(
                row >= 0,
                row <= base.len(),
                out == fixed_out_fn(base[:row], active[:row])
            )
    return InvGrammar(matrix_computation_inv0_grammar_fn, [])

def get_matrix_computation_inv1_grammar(
    fixed_grammar: bool,
    fixed_row_vec_fn: Optional[Any] = None, # TODO(jie): add type for this
    fixed_out_fn: Optional[Any] = None, # TODO(jie): add type for this
    constants: Optional[List[Int]] = None,
    compute_ops: Optional[List[str]] = None,
    depth: Optional[int] = None,
):
    if fixed_grammar:
        if fixed_row_vec_fn is None:
            raise Exception("Must pass in an override row_vec!")
        if fixed_out_fn is None:
            raise Exception("Must pass in an override out!")
    def matrix_computation_inv1_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
        # inner loop grammar
        col, pixel, row_vec = writes
        out, row = in_scope
        base, active = reads
        if not fixed_grammar:
            index_lower_bound = choose(Int(0), Int(1))
            index_upper_bound = choose(base.len(), base[0].len())
            outer_index_lower_cond = choose(
                row >= index_lower_bound,
                row > index_lower_bound,
                row == index_lower_bound,
                row < index_lower_bound,
                row <= index_lower_bound
            )
            outer_index_upper_cond = choose(
                row >= index_upper_bound,
                row > index_upper_bound,
                row == index_upper_bound,
                row < index_upper_bound,
                row <= index_upper_bound
            )
            inner_index_lower_cond = choose(
                col >= index_lower_bound,
                col > index_lower_bound,
                col == index_lower_bound,
                col < index_lower_bound,
                col <= index_lower_bound
            )
            inner_index_upper_cond = choose(
                col >= index_upper_bound,
                col > index_upper_bound,
                col == index_upper_bound,
                col < index_upper_bound,
                col <= index_upper_bound
            )
            vec_choices = [
                base[0][:col],
                base[row][:col],
                base[col][:row],
                base[0][:row],
                active[0][:col],
                active[row][:col],
                active[col][:row],
                active[0][:row],
                row_vec
            ]
            matrix_choices = [
                base,
                base[:row],
                base[:col],
                active,
                active[:row],
                active[:col]
            ]
            return and_objects(
                outer_index_lower_cond,
                outer_index_upper_cond,
                inner_index_lower_cond,
                inner_index_upper_cond,
                row_vec == vec_computation(
                    args=vec_choices,
                    constants=constants,
                    compute_ops=compute_ops,
                    depth=depth
                ),
                out == matrix_computation(
                    args=matrix_choices,
                    constants=constants,
                    compute_ops=compute_ops,
                    depth=depth
                )
            )
        else:
            return and_objects(
                row >= 0,
                row < base.len(),
                col >= 0,
                col <= base[0].len(),
                row_vec == fixed_row_vec_fn(base[row][:col], active[row][:col]),
                out == fixed_out_fn(base[:row], active[:row])
            )
    return InvGrammar(
        matrix_computation_inv1_grammar_fn,
        ["row", "agg.result"]
    )

def get_matrix_computation_with_counts_ps_grammar_fn(
    fixed_grammar: bool,
    fixed_out_fn: Optional[Any] = None, # TODO(jie): add type for this
    constants: Optional[List[Int]] = None,
    ordered_compute_ops: Optional[OrderedDict] = None,
    depth: Optional[int] = None,
) -> Callable[[List[Object], List[Object], List[Object]], Bool]:
    if fixed_grammar and fixed_out_fn is None:
        raise Exception("Must pass in an override out!")
    def matrix_computation_ps_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
        ret_val = writes[0]
        base, active = reads
        if not fixed_grammar:
            return ret_val == computation_with_counts(
                args=[base, active],
                constants=constants,
                ordered_compute_ops=ordered_compute_ops,
                depth=depth,
                is_vec=False
            )
        else:
            return ret_val == fixed_out_fn(base, active)
    return matrix_computation_ps_grammar_fn

def get_matrix_computation_with_counts_inv0_grammar(
    fixed_grammar: bool,
    fixed_out_fn: Optional[Any] = None, # TODO(jie): add type for this
    constants: Optional[List[Int]] = None,
    ordered_compute_ops: Optional[OrderedDict] = None,
    depth: Optional[int] = None,
) -> InvGrammar:
    if fixed_grammar:
        if fixed_out_fn is None:
            raise Exception("Must pass in an override out!")
    def matrix_computation_inv0_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
        # outer loop grammar
        out, col, pixel, row, row_vec = writes
        base, active = reads
        if not fixed_grammar:
            index_lower_bound = choose(Int(0), Int(1))
            index_upper_bound = choose(base.len(), base[0].len())
            index_lower_cond = choose(
                row >= index_lower_bound,
                # row > index_lower_bound,
                # row == index_lower_bound,
                # row < index_lower_bound,
                # row <= index_lower_bound
            )
            index_upper_cond = choose(
                # row >= index_upper_bound,
                # row > index_upper_bound,
                # row == index_upper_bound,
                # row < index_upper_bound,
                row <= index_upper_bound
            )
            matrix_choices = [
                # base,
                base[:row],
                base[:col],
                # active,
                active[:row],
                active[:col],
            ]
            return and_objects(
                index_lower_cond,
                index_upper_cond,
                out == computation_with_counts(
                    args=matrix_choices,
                    constants=constants,
                    ordered_compute_ops=ordered_compute_ops,
                    depth=depth,
                    is_vec=False
                )
            )
        else:
            return and_objects(
                row >= 0,
                row <= base.len(),
                out == fixed_out_fn(base[:row], active[:row])
            )
    return InvGrammar(matrix_computation_inv0_grammar_fn, [])

def get_matrix_computation_with_counts_inv1_grammar(
    fixed_grammar: bool,
    fixed_row_vec_fn: Optional[Any] = None, # TODO(jie): add type for this
    fixed_out_fn: Optional[Any] = None, # TODO(jie): add type for this
    constants: Optional[List[Int]] = None,
    ordered_compute_ops: Optional[OrderedDict] = None,
    depth: Optional[int] = None,
):
    if fixed_grammar:
        if fixed_row_vec_fn is None:
            raise Exception("Must pass in an override row_vec!")
        if fixed_out_fn is None:
            raise Exception("Must pass in an override out!")
    def matrix_computation_inv1_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
        # inner loop grammar
        col, pixel, row_vec = writes
        out, row = in_scope
        base, active = reads
        if not fixed_grammar:
            index_lower_bound = choose(Int(0), Int(1))
            index_upper_bound = choose(base.len(), base[0].len())
            outer_index_lower_cond = choose(
                row >= index_lower_bound,
                # row > index_lower_bound,
                # row == index_lower_bound,
                # row < index_lower_bound,
                # row <= index_lower_bound
            )
            outer_index_upper_cond = choose(
                # row >= index_upper_bound,
                # row > index_upper_bound,
                # row == index_upper_bound,
                row < index_upper_bound,
                row <= index_upper_bound
            )
            inner_index_lower_cond = choose(
                col >= index_lower_bound,
                # col > index_lower_bound,
                # col == index_lower_bound,
                # col < index_lower_bound,
                # col <= index_lower_bound
            )
            inner_index_upper_cond = choose(
                # col >= index_upper_bound,
                # col > index_upper_bound,
                # col == index_upper_bound,
                # col < index_upper_bound,
                col <= index_upper_bound
            )
            vec_choices = [
                # base[0][:col],
                base[row][:col],
                # base[col][:row],
                # base[0][:row],
                # active[0][:col],
                active[row][:col],
                # active[col][:row],
                # active[0][:row],
                # row_vec
            ]
            matrix_choices = [
                # base,
                base[:row],
                base[:col],
                # active,
                active[:row],
                active[:col]
            ]
            return and_objects(
                outer_index_lower_cond,
                outer_index_upper_cond,
                inner_index_lower_cond,
                inner_index_upper_cond,
                row_vec == computation_with_counts(
                    args=vec_choices,
                    constants=constants,
                    ordered_compute_ops=ordered_compute_ops,
                    depth=depth,
                    is_vec=True
                ),
                out == computation_with_counts(
                    args=matrix_choices,
                    constants=constants,
                    ordered_compute_ops=ordered_compute_ops,
                    depth=depth,
                    is_vec=False
                )
            )
        else:
            return and_objects(
                row >= 0,
                row < base.len(),
                col >= 0,
                col <= base[0].len(),
                row_vec == fixed_row_vec_fn(base[row][:col], active[row][:col]),
                out == fixed_out_fn(base[:row], active[:row])
            )
    return InvGrammar(
        matrix_computation_inv1_grammar_fn,
        ["row", "agg.result"]
    )

def matrix_computation_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        vec_elemwise_add,
        matrix_elemwise_add,
        vec_elemwise_sub,
        matrix_elemwise_sub,
        vec_elemwise_mul,
        matrix_elemwise_mul,
        vec_elemwise_div,
        matrix_elemwise_div,
        vec_scalar_add,
        matrix_scalar_add,
        vec_scalar_sub,
        matrix_scalar_sub,
        vec_scalar_mul,
        matrix_scalar_mul,
        vec_scalar_div,
        matrix_scalar_div
    ]

def get_matrix_computation_grammars_without_analysis(depth: int) -> Tuple[InvGrammar, InvGrammar, Callable[[List[Object], List[Object], List[Object]], Bool]]:
    return get_matrix_computation_grammars(
        fixed_grammar=False,
        constants=[Int(0), Int(2), Int(128), Int(32)],
        compute_ops=["+", "-", "*", "//"],
        depth=depth
    )

def get_matrix_computation_grammars(
    fixed_grammar: bool,
    fixed_row_vec_fn: Optional[Any] = None, # TODO(jie): add type for this
    fixed_out_fn: Optional[Any] = None, # TODO(jie): add type for this
    constants: Optional[List[Int]] = None,
    compute_ops: Optional[List[str]] = None,
    depth: Optional[int] = None,
) -> Tuple[InvGrammar, InvGrammar, Callable[[List[Object], List[Object], List[Object]], Bool]]:
    inv0_grammar = get_matrix_computation_inv0_grammar(
            fixed_grammar=fixed_grammar,
            fixed_out_fn=fixed_out_fn,
            constants=constants,
            compute_ops=compute_ops,
            depth=depth
        )
    inv1_grammar = get_matrix_computation_inv1_grammar(
        fixed_grammar=fixed_grammar,
        fixed_row_vec_fn=fixed_row_vec_fn,
        fixed_out_fn=fixed_out_fn,
        constants=constants,
        ordered_compute_ops=compute_ops,
        depth=depth
    )
    ps_grammar = get_matrix_computation_ps_grammar_fn(
        fixed_grammar=fixed_grammar,
        fixed_out_fn=fixed_out_fn,
        constants=constants,
        compute_ops=compute_ops,
        depth=depth
    )
    return inv0_grammar, inv1_grammar, ps_grammar

def get_select_two_args_synth_without_analysis(depth: int) -> Synth:
    return get_select_two_args_general_synth(
        args=[int_x, int_y],
        constants=[Int(0), Int(2), Int(128), Int(32)],
        compute_ops=["+", "-", "*", "//"],
        compare_ops=[">=", ">", "==", "<", "<="],
        depth=depth
    )

def get_complement_tuple(total: Tuple[int], curr: Tuple[int]) -> Tuple[int]:
    if len(total) != len(curr):
        raise Exception("Cannot get complement tuple with different length")
    return tuple(total[i] - curr[i] for i in range(len(total)))

def make_dict(keys: Tuple[str], values: Tuple[int]) -> OrderedDict:
    if len(keys) != len(values):
        raise Exception("Cannot make dictionary from keys and values of different length!")
    return OrderedDict(
        {keys[i]: values[i] for i in range(len(keys))}
    )

def helper_with_counts(
    args: List[Int],
    constants: List[Int],
    ordered_compute_ops: OrderedDict,
    depth: int
) -> Optional[Object]:
    if depth == 0:
        return choose(*args, *constants)
    if all(count == 0 for count in ordered_compute_ops.values()):
        return None

    # First fix left hand side to be depth - 1
    choices: Set[ObjectWrapper] = set()
    one_side_depth = depth - 1

    symmetric_ops = ["+", "*"]
    asymmetric_ops = ["-", "//"]

    one_side_depth = depth - 1
    # The other depth can be anywhere from 0 to depth - 1
    for other_side_depth in range(depth):
        for op in symmetric_ops + asymmetric_ops:
            if (op_count := ordered_compute_ops.get(op, 0)) == 0:
                continue
            visited_combs: Set[Tuple[Tuple[int], Tuple[int]]] = set()
            ordered_compute_ops_copy = copy.deepcopy(ordered_compute_ops)
            ordered_compute_ops_copy[op] = op_count - 1
            ranges = [range(0, count + 1) for count in ordered_compute_ops_copy.values()]
            all_combs = set(product(*ranges))
            for comb in all_combs:
                comp_comb = get_complement_tuple(
                    tuple(ordered_compute_ops_copy.values()),
                    comb
                )
                ordered_ops = tuple(ordered_compute_ops.keys())
                compute_ops_from_comb = make_dict(ordered_ops, comb)
                compute_ops_from_comp_comb = make_dict(ordered_ops, comp_comb)
                one_side = helper_with_counts(args, constants, compute_ops_from_comb, one_side_depth)
                other_side = helper_with_counts(args, constants, compute_ops_from_comp_comb, other_side_depth)
                if one_side is None or other_side is None:
                    continue
                if op in symmetric_ops:
                    if (comb, comp_comb) not in visited_combs:
                        if op == "+":
                            choices.add(ObjectWrapper(one_side + other_side))
                        if op == "*":
                            choices.add(ObjectWrapper(one_side * other_side))
                        visited_combs.add((comb, comp_comb))
                        visited_combs.add((comp_comb, comb))
                elif op in asymmetric_ops:
                    if (comb, comp_comb) not in visited_combs:
                        if op == "-":
                            choices.add(ObjectWrapper(one_side - other_side))
                        if op == "//":
                            choices.add(ObjectWrapper(one_side // other_side))
                        visited_combs.add((comb, comp_comb))
                    if (comp_comb, comb) not in visited_combs:
                        if op == "-":
                            choices.add(ObjectWrapper(other_side - one_side))
                        if op == "//":
                            choices.add(ObjectWrapper(other_side // one_side))
                        visited_combs.add((comp_comb, comb))

    if len(choices) == 0:
        return None
    return choose(*[choice.object for choice in choices])

def helper_with_counts_and_constants(
    args: List[Int],
    constants: List[Int],
    ordered_compute_ops: OrderedDict,
    depth: int
) -> Optional[Object]:
    if depth == 0:
        return choose(*args, *constants)
    if all(count == 0 for count in ordered_compute_ops.values()):
        return None

    # First fix left hand side to be depth - 1
    choices: Set[ObjectWrapper] = set()
    one_side_depth = depth - 1

    symmetric_ops = ["+", "*"]
    asymmetric_ops = ["-", "//"]

    one_side_depth = depth - 1
    # The other depth can be anywhere from 0 to depth - 1
    for other_side_depth in range(depth):
        for (arg1, op, arg2), op_count in ordered_compute_ops.items():
            if op_count == 0:
                continue
            visited_combs: Set[Tuple[Tuple[int], Tuple[int]]] = set()
            ordered_compute_ops_copy = copy.deepcopy(ordered_compute_ops)
            ordered_compute_ops_copy[(arg1, op, arg2)] = op_count - 1
            ranges = [range(0, count + 1) for count in ordered_compute_ops_copy.values()]
            all_combs = set(product(*ranges))
            for comb in all_combs:
                comp_comb = get_complement_tuple(
                    tuple(ordered_compute_ops_copy.values()),
                    comb
                )
                ordered_ops = tuple(ordered_compute_ops.keys())
                compute_ops_from_comb = make_dict(ordered_ops, comb)
                compute_ops_from_comp_comb = make_dict(ordered_ops, comp_comb)
                one_side = helper_with_counts_and_constants(args, constants, compute_ops_from_comb, one_side_depth)
                other_side = helper_with_counts_and_constants(args, constants, compute_ops_from_comp_comb, other_side_depth)
                if op in symmetric_ops:
                    if (comb, comp_comb) not in visited_combs:
                        if op == "+":
                            # For now we assume that we don't have constant + constant
                            if arg2 is not None or arg1 is not None:
                                if one_side is None or other_side_depth != 0:
                                    continue
                                if arg1 is not None:
                                    choices.add(ObjectWrapper(one_side + arg1))
                                else:
                                    # arg2 must not be None
                                    choices.add(ObjectWrapper(one_side + arg2))
                            else:
                                if one_side is None or other_side is None:
                                    continue
                                choices.add(ObjectWrapper(one_side + other_side))
                        if op == "*":
                            if arg2 is not None or arg1 is not None:
                                if one_side is None or other_side_depth != 0:
                                    continue
                                if arg1 is not None:
                                    choices.add(ObjectWrapper(one_side * arg1))
                                else:
                                    # arg2 must not be None
                                    choices.add(ObjectWrapper(one_side * arg2))
                            else:
                                if one_side is None or other_side is None:
                                    continue
                                choices.add(ObjectWrapper(one_side * other_side))
                        visited_combs.add((comb, comp_comb))
                        visited_combs.add((comp_comb, comb))
                elif op in asymmetric_ops:
                    if (comb, comp_comb) not in visited_combs:
                        if op == "-":
                            if arg1 is not None or arg2 is not None:
                                if one_side is None or other_side_depth != 0 or arg2 is None:
                                    continue
                                choices.add(ObjectWrapper(one_side - arg2))
                            else:
                                if one_side is None or other_side is None:
                                    continue
                                choices.add(ObjectWrapper(one_side - other_side))
                        if op == "//":
                            if arg1 is not None or arg2 is not None:
                                if one_side is None or other_side_depth != 0 or arg2 is None:
                                    continue
                                choices.add(ObjectWrapper(one_side // arg2))
                            else:
                                if one_side is None or other_side is None:
                                    continue
                                choices.add(ObjectWrapper(one_side // other_side))
                        visited_combs.add((comb, comp_comb))
                    if (comp_comb, comb) not in visited_combs:
                        if op == "-":
                            if arg1 is not None or arg2 is not None:
                                if one_side is None or other_side_depth != 0 or arg1 is None:
                                    continue
                                choices.add(ObjectWrapper(arg1 - one_side))
                            else:
                                if one_side is None or other_side is None:
                                    continue
                                choices.add(ObjectWrapper(other_side - one_side))
                        if op == "//":
                            if arg1 is not None or arg2 is not None:
                                if one_side is None or other_side_depth != 0 or arg1 is None:
                                    continue
                                choices.add(ObjectWrapper(arg1 // one_side))
                            else:
                                if one_side is None or other_side is None:
                                    continue
                                choices.add(ObjectWrapper(other_side // one_side))
                        visited_combs.add((comp_comb, comb))

    if len(choices) == 0:
        return None
    return choose(*[choice.object for choice in choices])

# @lru_cache(maxsize=None)
# TODO(jie): rename this function
def helper(
    args: List[Int],
    constants: List[Int],
    compute_ops: List[str],
    depth: int
) -> Object:
    if depth == 0:
        return choose(*args, *constants)

    # First fix left hand side to be depth - 1
    choices: List[Object] = []
    lhs_depth = depth - 1
    for rhs_depth in range(depth):
        lhs = helper(args, constants, compute_ops, lhs_depth)
        rhs = helper(args, constants, compute_ops, rhs_depth)
        if "+" in compute_ops:
            choices.append(lhs + rhs)
        if "*" in compute_ops:
            choices.append(lhs * rhs)
        if "-" in compute_ops:
            choices.append(lhs - rhs)
        if "//" in compute_ops:
            choices.append(lhs // rhs)
    # Then fix right hand side to be depth - 1
    rhs_depth = depth - 1
    for lhs_depth in range(depth - 1):
        # Skipping lhs_depth because we already visited this case in the last for loop
        lhs = helper(args, constants, compute_ops, lhs_depth)
        rhs = helper(args, constants, compute_ops, rhs_depth)
        if "-" in compute_ops:
            choices.append(lhs - rhs)
        if "//" in compute_ops:
            choices.append(lhs // rhs)
    return choose(*choices)

def get_sym_unique_int_exps_with_depth(
    symbols: List[Symbol],
    constants: List[symInt],
    compute_ops: List[str],
    depth: int
) -> Dict[int, symExpr]:
    if depth == 0:
        return {0: {*symbols, *constants}}
    lower_depths_exprs = get_sym_unique_int_exps_with_depth(symbols, constants, compute_ops, depth - 1)
    choices: Set[symExpr] = set()
    # First fix left hand side to be depth - 1
    lhs_exprs = lower_depths_exprs[depth - 1]
    for rhs_depth in range(depth):
        rhs_exprs = lower_depths_exprs[rhs_depth]
        expr_args = set(product(lhs_exprs, rhs_exprs))
        for arg1, arg2 in expr_args:
            if "+" in compute_ops:
                choices.add(arg1 + arg2)
            if "-" in compute_ops:
                choices.add(arg1 - arg2)
            if "*" in compute_ops:
                choices.add(arg1 * arg2)
            if "//" in compute_ops and arg2 != 0:
                choices.add(arg1 // arg2)

    return {
        **get_sym_unique_int_exps_with_depth(symbols, constants, compute_ops, depth - 1),
        depth: choices
    }

def get_unique_int_exps_with_depth(
    args: List[Int],
    constants: List[Int],
    compute_ops: List[str],
    depth: int
) -> Dict[int, Set[ObjectWrapper]]:
    args_wrappers = [ObjectWrapper(arg) for arg in args]
    constants_wrappers = [ObjectWrapper(cons) for cons in constants]
    all_wrappers = [*args_wrappers, *constants_wrappers]

    if depth == 0:
        return {0: set(all_wrappers)}
    lower_depths_wrappers = get_unique_int_exps_with_depth(args, constants, compute_ops, depth - 1)
    choices: Set[ObjectWrapper] = set()
    lit_0_wrapper = ObjectWrapper(Int(0))
    lit_1_wrapper = ObjectWrapper(Int(1))
    # First fix left hand side to be depth - 1
    lhs_wrappers = lower_depths_wrappers[depth - 1]
    for rhs_depth in range(depth):
        if rhs_depth == depth - 1:
            add_mul_wrappers = combinations_with_replacement(lhs_wrappers, 2)
        else:
            add_mul_wrappers = set(product(lhs_wrappers, lower_depths_wrappers[rhs_depth]))
        for arg1, arg2 in add_mul_wrappers:
            # This is just to be safe
            if hash(arg1) > hash(arg2):
                arg1, arg2 = arg2, arg1
            if "+" in compute_ops:
                if arg1 != lit_0_wrapper and arg2 != lit_0_wrapper:
                    choices.add(ObjectWrapper(arg1.object + arg2.object))
            if "*" in compute_ops:
                if arg1 != lit_1_wrapper and arg2 != lit_1_wrapper:
                    choices.add(ObjectWrapper(arg1.object * arg2.object))

        sub_div_wrappers = set(product(lhs_wrappers, lower_depths_wrappers[rhs_depth]))
        for arg1, arg2 in sub_div_wrappers:
            if arg1 != arg2:
                if "-" in compute_ops:
                    if arg2 != lit_0_wrapper:
                        choices.add(ObjectWrapper(arg1.object - arg2.object))
                    if arg1 != lit_0_wrapper:
                        choices.add(ObjectWrapper(arg2.object - arg1.object))
                if "//" in compute_ops:
                    if arg2 not in {lit_0_wrapper, lit_1_wrapper} and arg1 != lit_0_wrapper:
                        choices.add(ObjectWrapper(arg1.object // arg2.object))
                    if arg1 not in {lit_0_wrapper, lit_1_wrapper} and arg2 != lit_0_wrapper:
                        choices.add(ObjectWrapper(arg2.object // arg1.object))

    return {
        **get_unique_int_exps_with_depth(args, constants, compute_ops, depth - 1),
        depth: choices
    }

def get_multi_depth_compute_with_counts_general_synth(
    args: List[Object],
    constants: List[Int],
    ordered_compute_ops: OrderedDict,
    depth: int
) -> Synth:
    body = helper_with_counts(args, constants, ordered_compute_ops, depth)
    return synth(
        SELECT_TWO_ARGS,
        body,
        *args
    )

def get_multi_depth_with_counts_select_general_synth(
    args: List[Object],
    constants: List[Int],
    compare_ops: List[str],
    cond_lhs_depth: int,
    cond_rhs_depth: int,
    if_then_depth: int,
    if_else_depth: int,
    cond_lhs_ordered_compute_ops: OrderedDict,
    cond_rhs_ordered_compute_ops: OrderedDict,
    if_then_ordered_compute_ops: OrderedDict,
    if_else_ordered_compute_ops: OrderedDict
) -> Synth:
    cond_lhs = helper_with_counts(args, constants, cond_lhs_ordered_compute_ops, cond_lhs_depth)
    cond_rhs = helper_with_counts(args, constants, cond_rhs_ordered_compute_ops, cond_rhs_depth)
    if_then = helper_with_counts(args, constants, if_then_ordered_compute_ops, if_then_depth)
    if_else = helper_with_counts(args, constants, if_else_ordered_compute_ops, if_else_depth)

    cond_choices: List[Bool] = []
    if ">=" in compare_ops:
        cond_choices.append(cond_lhs >= cond_rhs)
    if ">" in compare_ops:
        cond_choices.append(cond_lhs > cond_rhs)
    if "==" in compare_ops:
        cond_choices.append(cond_lhs == cond_rhs)
    if "<" in compare_ops:
        cond_choices.append(cond_lhs < cond_rhs)
    if "<=" in compare_ops:
        cond_choices.append(cond_lhs <= cond_rhs)
    cond = choose(*cond_choices)
    return Synth(
        SELECT_TWO_ARGS,
        ite(cond, if_then, if_else).src,
        *get_object_exprs(*args[:2]) # TODO(jie): fix this, this is very hacky
    )

def get_multi_depth_with_counts_and_constants_select_general_synth(
    args: List[Object],
    constants: List[Int],
    compare_ops: List[str],
    cond_lhs_depth: int,
    cond_rhs_depth: int,
    if_then_depth: int,
    if_else_depth: int,
    cond_lhs_ordered_compute_ops: OrderedDict,
    cond_rhs_ordered_compute_ops: OrderedDict,
    if_then_ordered_compute_ops: OrderedDict,
    if_else_ordered_compute_ops: OrderedDict
) -> Synth:
    cond_lhs = helper_with_counts_and_constants(args, constants, cond_lhs_ordered_compute_ops, cond_lhs_depth)
    cond_rhs = helper_with_counts_and_constants(args, constants, cond_rhs_ordered_compute_ops, cond_rhs_depth)
    if_then = helper_with_counts_and_constants(args, constants, if_then_ordered_compute_ops, if_then_depth)
    if_else = helper_with_counts_and_constants(args, constants, if_else_ordered_compute_ops, if_else_depth)

    cond_choices: List[Bool] = []
    if ">=" in compare_ops:
        cond_choices.append(cond_lhs >= cond_rhs)
    if ">" in compare_ops:
        cond_choices.append(cond_lhs > cond_rhs)
    if "==" in compare_ops:
        cond_choices.append(cond_lhs == cond_rhs)
    if "<" in compare_ops:
        cond_choices.append(cond_lhs < cond_rhs)
    if "<=" in compare_ops:
        cond_choices.append(cond_lhs <= cond_rhs)
    cond = choose(*cond_choices)
    return Synth(
        SELECT_TWO_ARGS,
        ite(cond, if_then, if_else).src,
        *get_object_exprs(*args[:2]) # TODO(jie): fix this, this is very hacky
    )

def get_multi_depth_select_general_synth(
    args: List[Object],
    constants: List[Int],
    compute_ops: List[str],
    compare_ops: List[str],
    cond_lhs_depth: int,
    cond_rhs_depth: int,
    if_then_depth: int,
    if_else_depth: int,
) -> Synth:
    cond_lhs = helper(args, constants, compute_ops, cond_lhs_depth)
    cond_rhs = helper(args, constants, compute_ops, cond_rhs_depth)
    if_then = helper(args, constants, compute_ops, if_then_depth)
    if_else = helper(args, constants, compute_ops, if_else_depth)

    cond_choices: List[Bool] = []
    if ">=" in compare_ops:
        cond_choices.append(cond_lhs >= cond_rhs)
    if ">" in compare_ops:
        cond_choices.append(cond_lhs > cond_rhs)
    if "==" in compare_ops:
        cond_choices.append(cond_lhs == cond_rhs)
    if "<" in compare_ops:
        cond_choices.append(cond_lhs < cond_rhs)
    if "<=" in compare_ops:
        cond_choices.append(cond_lhs <= cond_rhs)
    cond = choose(*cond_choices)
    return Synth(
        SELECT_TWO_ARGS,
        ite(cond, if_then, if_else).src,
        *get_object_exprs(*args)
    )

def get_select_two_args_general_synth(
    args: List[Object],
    constants: List[Int],
    compute_ops: List[str],
    compare_ops: List[str],
    depth: int,
) -> Synth:
    # arg_or_cons = choose(arg_expr, Int(0), Int(32))
    # if_then_int_exp, if_else_int_exp = arg_or_cons, arg_or_cons
    # if_else_int_exp = choose(if_else_int_exp, if_else_int_exp - if_else_int_exp)
    # if_else_int_exp = choose(if_else_int_exp, if_else_int_exp // if_else_int_exp)
    # if_else_int_exp = choose(if_else_int_exp, if_else_int_exp - if_else_int_exp)
    # cond_int_exp = arg_or_cons
    # cond = choose(
    #     cond_int_exp >= cond_int_exp,
    #     cond_int_exp > cond_int_exp,
    #     cond_int_exp == cond_int_exp,
    #     cond_int_exp < cond_int_exp,
    #     cond_int_exp <= cond_int_exp
    # )
    # return Synth(
    #     SELECT_TWO_ARGS,
    #     ite(cond, if_then_int_exp, if_else_int_exp).src,
    #     *get_object_exprs(*args)
    # )
    int_exp = choose(*args, *constants)
    for _ in range(depth):
        possible_choices = [int_exp]
        if "+" in compute_ops:
            possible_choices.append(int_exp + int_exp)
        if "-" in compute_ops:
            possible_choices.append(int_exp - int_exp)
        if "*" in compute_ops:
            possible_choices.append(int_exp * int_exp)
        if "//" in compute_ops:
            possible_choices.append(int_exp // int_exp)
        int_exp = choose(*possible_choices)
    cond_choices: List[Bool] = []
    if ">=" in compare_ops:
        cond_choices.append(int_exp >= int_exp)
    if ">" in compare_ops:
        cond_choices.append(int_exp > int_exp)
    if "==" in compare_ops:
        cond_choices.append(int_exp == int_exp)
    if "<" in compare_ops:
        cond_choices.append(int_exp < int_exp)
    if "<=" in compare_ops:
        cond_choices.append(int_exp <= int_exp)
    cond = choose(*cond_choices)
    return Synth(
        SELECT_TWO_ARGS,
        ite(cond, int_exp, int_exp).src,
        *get_object_exprs(*args)
    )

def get_select_synth_from_hole(driver: Driver, hole_body: Callable[[Int], Int]) -> Synth:
    driver.add_var_objects([int_x, int_y])
    var = choose(int_x, int_y)
    return synth(
        SELECT_TWO_ARGS,
        hole_body(var),
        int_x,
        int_y
    )

def get_select_two_args_synth(select_bodies: List[Object], args: List[Object]) -> Synth:
    return synth(
        SELECT_TWO_ARGS,
        choose(*select_bodies),
        *args
    )

def get_map_int_to_int_synth(
    bodies: List[Object] = [call_integer_exp(int_x), call_integer_sqrt(int_x)]
) -> Synth:
    return synth(
        MAP_INT_TO_INT,
        choose(*bodies),
        int_x
    )

# Some **general** helper functions to get loop bounds.
outer_loop_left_bound_fn_name = "OUTER_LOOP_LEFT_BOUND"
outer_loop_right_bound_fn_name = "OUTER_LOOP_RIGHT_BOUND"

def get_lower_bound_fn_body(is_left_bound_smaller: Bool, left_bound: Int, right_bound: Int) -> Int:
    return ite(
        is_left_bound_smaller,
        left_bound,
        # (for i = {var}; i > {var}; i--): right_bound + 1
        # (for i = {var}; i >= {var}; i--): right_bound
        choose(right_bound, right_bound + 1)
    )

def get_upper_bound_fn_body(is_left_bound_smaller: Bool, left_bound: Int, right_bound: Int) -> Int:
    return ite(
        is_left_bound_smaller,
        # (for i = {var}; i < {var}; i++): right_bound - 1
        # (for i = {var}; i <= {var}; i++): right_bound
        choose(right_bound - 1, right_bound),
        left_bound
    ) + 1 # We add 1 here because the upper bound is exclusive

def get_loop_index_fn(
    loop_fn_args: List[Int],
    prefix: str = "OUTER_LOOP"
) -> Tuple[FnDecl, Synth, Callable]:
    index_fn_name = f"{prefix}_INDEX"
    index_fn_decl = fn_decl(
        index_fn_name,
        Int,
        None,
        *loop_fn_args
    )
    index_synth = synth(
        index_fn_name,
        choose(*loop_fn_args),
        *loop_fn_args
    )
    def get_loop_index(*args: Int) -> Int:
        return call(index_fn_name, Int, *args)

    return index_fn_decl, index_synth, get_loop_index

def get_loop_bound_fn(
    loop_fn_args: List[Int],
    body: Int,
    prefix: str = "OUTER_LOOP_LEFT"
) -> Tuple[FnDecl, Synth, Callable]:
    bound_fn_name = f"{prefix}_BOUND"
    bound_fn_decl = fn_decl(
        bound_fn_name,
        Int,
        None,
        *loop_fn_args
    )
    bound_synth = synth(
        bound_fn_name,
        body,
        *loop_fn_args
    )
    def get_loop_bound(*args: Int) -> Int:
        return call(bound_fn_name, Int, *args)
    return bound_fn_decl, bound_synth, get_loop_bound

def get_loop_fns(
    loop_bound_fn_args: List[Int],
    loop_index_fn_args: List[Int],
    left_bound_choices: List[Int],
    right_bound_choices: List[Int],
    prefix: str = "OUTER_LOOP"
) -> Tuple[
    List[FnDecl],
    List[Synth],
    Callable,
    Callable,
    Bool
]:
    # TODO(jie): add return type
    if prefix not in {"OUTER_LOOP", "INNER_LOOP"}:
        raise Exception("Prefix must be one of OUTER_LOOP and INNER_LOOP")

    index_fn_decl, index_synth, get_index = get_loop_index_fn(loop_index_fn_args, prefix)

    is_left_bound_smaller_fn_name = f"{prefix}_IS_LEFT_BOUND_SMALLER"
    is_left_bound_smaller_fn_decl, is_left_bound_smaller_synth = get_no_arg_bool_fn(is_left_bound_smaller_fn_name)
    is_left_bound_smaller = call(is_left_bound_smaller_fn_name, Bool)

    left_bound_prefix = f"{prefix}_LEFT"
    right_bound_prefix = f"{prefix}_RIGHT"
    lower_bound_prefix = f"{prefix}_LOWER"
    upper_bound_prefix = f"{prefix}_UPPER"
    left_bound_fn_decl, left_bound_synth, get_left_bound = get_loop_bound_fn(
        loop_bound_fn_args,
        choose(*left_bound_choices),
        left_bound_prefix
    )
    right_bound_fn_decl, right_bound_synth, get_right_bound = get_loop_bound_fn(
        loop_bound_fn_args,
        choose(*right_bound_choices),
        right_bound_prefix
    )
    lower_bound_fn_decl, lower_bound_synth, get_lower_bound = get_loop_bound_fn(
        loop_bound_fn_args,
        get_lower_bound_fn_body(
            is_left_bound_smaller,
            get_left_bound(*loop_bound_fn_args),
            get_right_bound(*loop_bound_fn_args)
        ),
        lower_bound_prefix
    )
    upper_bound_fn_decl, upper_bound_synth, get_upper_bound = get_loop_bound_fn(
        loop_bound_fn_args,
        get_upper_bound_fn_body(
            call(is_left_bound_smaller_fn_name, Bool),
            get_left_bound(*loop_bound_fn_args),
            get_right_bound(*loop_bound_fn_args)
        ),
        upper_bound_prefix
    )

    all_decls = [
        index_fn_decl,
        is_left_bound_smaller_fn_decl,
        left_bound_fn_decl,
        right_bound_fn_decl,
        lower_bound_fn_decl,
        upper_bound_fn_decl
    ]
    all_synths = [
        index_synth,
        is_left_bound_smaller_synth,
        left_bound_synth,
        right_bound_synth,
        lower_bound_synth,
        upper_bound_synth
    ]
    return all_decls, all_synths, get_lower_bound, get_upper_bound, get_index, is_left_bound_smaller

def get_no_arg_bool_fn(fn_name: str) -> Tuple[FnDecl, Synth, Callable]:
    bool_fn_decl = fn_decl(fn_name, Bool, None)
    bool_fn_synth = synth(fn_name, choose(Bool(True), Bool(False)))
    def call_fn() -> Bool:
        return call(fn_name, Bool)
    return bool_fn_decl, bool_fn_synth, call_fn