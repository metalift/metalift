import copy
import typing
from typing import Any, Callable, Dict, Generator, List, Optional, Tuple, Union

from pyparsing import Set

from metalift.frontend.llvm import InvGrammar
from metalift.frontend.utils import ObjectSet
from metalift.ir import Bool, Fn, FnDecl, FnDeclRecursive, Int, ObjectWrapper, is_matrix_type, synth
from metalift.ir import List as mlList
from metalift.ir import (Matrix, Object, Synth, call, call_value, choose,
                         fn_decl, fn_decl_recursive, get_list_element_type,
                         get_object_exprs, is_list_type,
                         is_primitive_type, ite)
from metalift.vc_util import and_objects, or_objects
from itertools import product, combinations, permutations, combinations_with_replacement
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
NESTED_LIST_ELEMWISE_ADD = "nested_list_elemwise_add"
VEC_ELEMWISE_SUB = "vec_elemwise_sub"
NESTED_LIST_ELEMWISE_SUB = "nested_list_elemwise_sub"
VEC_ELEMWISE_MUL = "vec_elemwise_mul"
NESTED_LIST_ELEMWISE_MUL = "nested_list_elemwise_mul"
VEC_ELEMWISE_DIV = "vec_elemwise_div"
NESTED_LIST_ELEMWISE_DIV = "nested_list_elemwise_div"

# Scalar functions
VEC_SCALAR_ADD = "vec_scalar_add"
NESTED_LIST_SCALAR_ADD = "nested_list_scalar_add"
VEC_SCALAR_MUL = "vec_scalar_mul"
NESTED_LIST_SCALAR_MUL = "nested_list_scalar_mul"
# scalar on the right hand side
VEC_SCALAR_DIV = "vec_scalar_div"
NESTED_LIST_SCALAR_DIV = "nested_list_scalar_div"
VEC_SCALAR_SUB = "vec_scalar_sub"
NESTED_LIST_SCALAR_SUB = "nested_list_scalar_sub"

# Selection functions
SELECT_TWO_ARGS = "select_two_args"
SELECT_TWO_ARGS_ARG = "select_two_args_arg"
FIXED_SELECT_TWO_ARGS = "fixed_select_two_args"
SELECTION_TWO_ARGS = "selection_two_args"
NESTED_SELECTION_TWO_ARGS = "nested_selection_two_args"

# Uninterpreted functions
TEST_EXP_FN_NAME = "test_exp"
UNINTERP_DIV_FN_NAME = "uninterp_div"

# Operations that involve uninterpreted functions
VEC_MAP_TEST_EXP_FN_NAME = "map_test_exp"
NESTED_LIST_MAP_TEST_EXP_FN_NAME = "nested_list_map_exp"

# Other helper functions
MATRIX_VEC_MUL = "matrix_vec_mul"

MatrixOrVecT = Union[mlList[Int], Matrix[Int]]

def call_elemwise_add(left: MatrixOrVecT, right: MatrixOrVecT) -> MatrixOrVecT:
    if is_matrix_type(left.type):
        return call_nested_list_elemwise_add(left, right)
    else:
        return call_vec_elemwise_add(left, right)

def call_elemwise_sub(left: MatrixOrVecT, right: MatrixOrVecT) -> MatrixOrVecT:
    if is_matrix_type(left.type):
        return call_nested_list_elemwise_sub(left, right)
    else:
        return call_vec_elemwise_sub(left, right)

def call_elemwise_mul(left: MatrixOrVecT, right: MatrixOrVecT) -> MatrixOrVecT:
    if is_matrix_type(left.type):
        return call_nested_list_elemwise_mul(left, right)
    else:
        return call_vec_elemwise_mul(left, right)

def call_elemwise_div(left: MatrixOrVecT, right: MatrixOrVecT) -> MatrixOrVecT:
    if is_matrix_type(left.type):
        return call_nested_list_elemwise_div(left, right)
    else:
        return call_vec_elemwise_div(left, right)

def call_scalar_add(scalar: Int, matrix_or_vec: MatrixOrVecT) -> MatrixOrVecT:
    if is_matrix_type(matrix_or_vec.type):
        return call_nested_list_scalar_add(scalar, matrix_or_vec)
    else:
        return call_vec_scalar_add(scalar, matrix_or_vec)

def call_scalar_sub(scalar: Int, matrix_or_vec: MatrixOrVecT) -> MatrixOrVecT:
    if is_matrix_type(matrix_or_vec.type):
        return call_nested_list_scalar_sub(scalar, matrix_or_vec)
    else:
        return call_vec_scalar_sub(scalar, matrix_or_vec)

def call_scalar_mul(scalar: Int, matrix_or_vec: MatrixOrVecT) -> MatrixOrVecT:
    if is_matrix_type(matrix_or_vec.type):
        return call_nested_list_scalar_mul(scalar, matrix_or_vec)
    else:
        return call_vec_scalar_mul(scalar, matrix_or_vec)

def call_scalar_div(scalar: Int, matrix_or_vec: MatrixOrVecT) -> MatrixOrVecT:
    if is_matrix_type(matrix_or_vec.type):
        return call_nested_list_scalar_div(scalar, matrix_or_vec)
    else:
        return call_vec_scalar_div(scalar, matrix_or_vec)

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

def call_vec_scalar_mul(scalar: Int, vec: mlList[Int]) -> mlList[Int]:
    return call(VEC_SCALAR_MUL, mlList[Int], scalar, vec)

def call_vec_scalar_div(scalar: Int, vec: mlList[Int]) -> mlList[Int]:
    return call(VEC_SCALAR_DIV, mlList[Int], scalar, vec)

def call_vec_scalar_sub(scalar: Int, vec: mlList[Int]) -> mlList[Int]:
    return call(VEC_SCALAR_SUB, mlList[Int], scalar, vec)

def call_nested_list_elemwise_add(left: Matrix[Int], right: Matrix[Int]) -> Matrix[Int]:
    return call(NESTED_LIST_ELEMWISE_ADD, Matrix[Int], left, right)

def call_nested_list_elemwise_sub(left: Matrix[Int], right: Matrix[Int]) -> Matrix[Int]:
    return call(NESTED_LIST_ELEMWISE_SUB, Matrix[Int], left, right)

def call_nested_list_elemwise_mul(left: Matrix[Int], right: Matrix[Int]) -> Matrix[Int]:
    return call(NESTED_LIST_ELEMWISE_MUL, Matrix[Int], left, right)

def call_nested_list_elemwise_div(left: Matrix[Int], right: Matrix[Int]) -> Matrix[Int]:
    return call(NESTED_LIST_ELEMWISE_DIV, Matrix[Int], left, right)

def call_nested_list_scalar_add(scalar: Int, nested_list: Matrix[Int]) -> Matrix[Int]:
    return call(NESTED_LIST_SCALAR_ADD, Matrix[Int], scalar, nested_list)

def call_nested_list_scalar_mul(scalar: Int, nested_list: Matrix[Int]) -> Matrix[Int]:
    return call(NESTED_LIST_SCALAR_MUL, Matrix[Int], scalar, nested_list)

def call_nested_list_scalar_div(scalar: Int, nested_list: Matrix[Int]) -> Matrix[Int]:
    return call(NESTED_LIST_SCALAR_DIV, Matrix[Int], scalar, nested_list)

def call_nested_list_scalar_sub(scalar: Int, nested_list: Matrix[Int]) -> Matrix[Int]:
    return call(NESTED_LIST_SCALAR_SUB, Matrix[Int], scalar, nested_list)

def call_reduce_sum(lst) -> Int:
    return call(REDUCESUM, Int, lst)

def call_reduce_mul(lst) -> Int:
    return call(REDUCEMUL, Int, lst)

def call_reduce_max(lst) -> Int:
    return call(REDUCEMAX, Int, lst)

def call_selection_two_args(
    left: mlList[Int],
    right: mlList[Int],
    select_fn: Fn[typing.Tuple[Int, Int, Int]]
) -> mlList[Int]:
    return call(SELECTION_TWO_ARGS, mlList[Int], left, right, select_fn)

def call_nested_selection_two_args(
    left: Matrix[Int],
    right: Matrix[Int],
    select_fn: Fn[typing.Tuple[Int, Int, Int]]
) -> Matrix[Int]:
    return call(NESTED_SELECTION_TWO_ARGS, Matrix[Int], left, right, select_fn)

def call_exp(x: Int) -> Int:
    return call(TEST_EXP_FN_NAME, Int, x)

def call_vec_map_exp(x: mlList[Int]) -> mlList[Int]:
    return call(VEC_MAP_TEST_EXP_FN_NAME, mlList[Int], x)

def call_nested_list_map_exp(x: Matrix[Int]) -> Matrix[Int]:
    return call(NESTED_LIST_MAP_TEST_EXP_FN_NAME, Matrix[Int], x)

def call_uninterp_div(x: Int, y: Int) -> Int:
    return call(UNINTERP_DIV_FN_NAME, Int, x, y)

def call_matrix_vec_mul(matrix: Matrix[Int], vec: mlList[Int]) -> mlList[Int]:
    return call(MATRIX_VEC_MUL, mlList[Int], matrix, vec)

an_arr2_to_arr = lambda left, right: choose(
    call_vec_elemwise_add(left, right),
    call_vec_elemwise_sub(left, right),
    call_vec_elemwise_mul(left, right),
    call_vec_elemwise_div(left, right)
)
an_int_and_arr_to_arr = lambda num, arr: choose(
    call_vec_scalar_add(num, arr),
    # call_vec_scalar_sub(num, arr),
    call_vec_scalar_mul(num, arr),
    # call_vec_scalar_div(num, arr)
)
an_arr_to_int = lambda arr: choose(
    call_reduce_sum(arr),
    call_reduce_mul(arr),
    call_reduce_max(arr)
)
an_arr_to_arr = lambda arr: choose(
    call_vec_map_exp(arr)
)
a_matrix_and_vec_to_vec = lambda matrix, arr: choose(
    call_matrix_vec_mul(matrix, arr)
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

def nested_list_computation(
    args: List[Matrix[Int]],
    constants: List[Int],
    compute_ops: List[str],
    depth: int
) -> Matrix[Int]:
    op_to_scalar_call_mapping = {
        "+": call_nested_list_scalar_add,
        "-": call_nested_list_scalar_sub,
        "*": call_nested_list_scalar_mul,
        "//": call_nested_list_scalar_div,
    }
    op_to_elemwise_call_mapping = {
        "+": call_nested_list_elemwise_add,
        "-": call_nested_list_elemwise_sub,
        "*": call_nested_list_elemwise_mul,
        "//": call_nested_list_elemwise_div,
    }
    nested_list = choose(*args)
    cons = None
    if len(constants) > 0:
        cons = choose(*constants)
    for _ in range(depth):
        choices = [nested_list]
        for op in compute_ops:
            if cons is not None:
                choices.append(op_to_scalar_call_mapping[op](cons, nested_list))
            choices.append(op_to_elemwise_call_mapping[op](nested_list, nested_list))
        nested_list = choose(*choices)
    return nested_list

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
            "+": call_nested_list_scalar_add,
            "-": call_nested_list_scalar_sub,
            "*": call_nested_list_scalar_mul,
            "//": call_nested_list_scalar_div,
        }
        op_to_elemwise_call_mapping = {
            "+": call_nested_list_elemwise_add,
            "-": call_nested_list_elemwise_sub,
            "*": call_nested_list_elemwise_mul,
            "//": call_nested_list_elemwise_div,
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
nested_x = Matrix(Int, "nested_x")
nested_y = Matrix(Int, "nested_y")
int_x = Int("int_x")
int_y = Int("int_y")

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
matrix_vec_mul = fn_decl_recursive(MATRIX_VEC_MUL, mlList[Int], matrix_vec_mul_body(nested_x, x), nested_x, x)

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

def nested_list_mul8x8_div32_body(nested_x: Matrix[Int], nested_y: Matrix[Int]) -> Matrix[Int]:
    return call_nested_list_scalar_div(
        Int(32),
        call_nested_list_elemwise_mul(nested_x, nested_y)
    )

def vec_screen8x8_body(x: mlList[Int], y: mlList[Int]) -> mlList[Int]:
    return call_vec_elemwise_sub(
        call_vec_elemwise_add(x, y),
        vec_mul8x8_div32_body(x, y)
    )

def nested_list_screen8x8_body(nested_x: Matrix[Int], nested_y: Matrix[Int]) -> Matrix[Int]:
    return call_nested_list_elemwise_sub(
        call_nested_list_elemwise_add(nested_x, nested_y),
        nested_list_mul8x8_div32_body(nested_x, nested_y)
    )

def vec_linear_burn_body(x: mlList[Int], y: mlList[Int]) -> mlList[Int]:
    return call_vec_scalar_sub(
        Int(32),
        call_vec_elemwise_add(x, y),
    )

def nested_list_linear_burn_body(nested_x: Matrix[Int], nested_y: Matrix[Int]) -> Matrix[Int]:
    return call_nested_list_scalar_sub(
        Int(32),
        call_nested_list_elemwise_add(nested_x, nested_y)
    )

# Helper functions for compute benchmarks using the holing approach
def screen8x8_hole_body(
    matrix_or_vecs: List[MatrixOrVecT],
    constants: List[Int]
) -> MatrixOrVecT:
    matrix_or_vec = choose(*matrix_or_vecs)
    cons = choose(*constants)
    return call_elemwise_sub(
        call_elemwise_add(matrix_or_vec, matrix_or_vec),
        call_scalar_div(
            cons,
            call_elemwise_mul(matrix_or_vec, matrix_or_vec)
        )
    )

# Selection criteria
def select_darken_blend_body(int_x: Int, int_y: Int) -> Int:
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

def get_select_two_args_synth(select_bodies: List[Object], args: List[Object]) -> Synth:
    return Synth(
        SELECT_TWO_ARGS,
        choose(*select_bodies).src,
        *get_object_exprs(*args)
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

def nested_selection_two_args_body(
    left: Matrix[Int],
    right: Matrix[Int],
    select_fn: Fn[typing.Tuple[Int, Int, Int]]
) -> Matrix[Int]:
    cur = call_selection_two_args(left[0], right[0], select_fn)
    recursed = call_nested_selection_two_args(left[1:], right[1:], select_fn)
    general_answer = recursed.prepend(cur)
    return ite(
        or_objects(left.len() < 1, left.len() != right.len()),
        Matrix.empty(Int),
        general_answer
    )
nested_selection_two_args_fn_decl = fn_decl_recursive(
    NESTED_SELECTION_TWO_ARGS,
    Matrix[Int],
    nested_selection_two_args_body(nested_x, nested_y, select_two_args_fn_obj_arg),
    nested_x,
    nested_y,
    select_two_args_fn_obj_arg
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
    return ret_val == call_nested_selection_two_args(base_or_active, base_or_active, select_two_args_fn_obj)

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
    # return and_objects(
    #     row >= 0,
    #     row <= base.len(),
    #     out == call_nested_selection_two_args(
    #         base[:row],
    #         active[:row],
    #         fixed_select_two_args_fn_obj
    #     )
    # )
    index_lower_bound = choose(Int(0), Int(1))
    index_upper_bound = choose(base.len(), base[0].len(), active.len(), active[0].len())
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
    nested_list = choose(
        # base,
        base[:row],
        base[:col],
        # active,
        active[:row],
        active[:col],
    )
    return and_objects(
        index_lower_cond,
        index_upper_cond,
        out == call_nested_selection_two_args(nested_list, nested_list, select_two_args_fn_obj)
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
    # return and_objects(
    #     row >= 0,
    #     row < base.len(),
    #     col >= 0,
    #     col <= base[0].len(),
    #     row_vec == call_selection_two_args(
    #         base[row][:col],
    #         active[row][:col],
    #         fixed_select_two_args_fn_obj
    #     ),
    #     out == call_nested_selection_two_args(
    #         base[:row],
    #         active[:row],
    #         fixed_select_two_args_fn_obj
    #     )
    # )
    index_lower_bound = choose(Int(0), Int(1))
    index_upper_bound = choose(base.len(), base[0].len(), active.len(), active[0].len())
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
        # row <= index_upper_bound
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
    vec = choose(
        # base[0][:col],
        base[row][:col],
        # base[col][:row],
        # base[0][:row],
        # active[0][:col],
        active[row][:col],
        # active[col][:row],
        # active[0][:row],
    )
    nested_list = choose(
        # base,
        base[:row],
        base[:col],
        # active,
        active[:row],
        active[:col]
    )
    return and_objects(
        outer_index_lower_cond,
        outer_index_upper_cond,
        inner_index_lower_cond,
        inner_index_upper_cond,
        row_vec == call_selection_two_args(vec, vec, select_two_args_fn_obj),
        out == call_nested_selection_two_args(nested_list, nested_list, select_two_args_fn_obj)
    )

def selection_two_args_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        select_two_args_fn_decl,
        # fixed_select_two_args_fn_decl,
        selection_two_args_fn_decl,
        nested_selection_two_args_fn_decl
    ]

selection_two_args_inv0_grammar = InvGrammar(selection_two_args_inv0_grammar_fn, [])
selection_two_args_inv1_grammar = InvGrammar(selection_two_args_inv1_grammar_fn, ["row", "agg.result"])

def elemwise_body(
    left: Union[mlList[Int], Matrix[Int]],
    right: Union[mlList[Int], Matrix[Int]],
    compute_fn: Callable[[Int, Int], Int],
    vec_fn_name: str,
    nested_list_fn_name: str
) -> Union[mlList[Int], Matrix[Int]]:
    if is_matrix_type(left.type) and is_matrix_type(right.type):
        cur = call(vec_fn_name, mlList[Int], left[0], right[0])
        recursed = call(nested_list_fn_name, Matrix[Int], left[1:], right[1:])
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
    vec_or_nested_list: Union[mlList[Int], Matrix[Int]],
    compute_fn: Callable[[Int, Int], Int],
    vec_fn_name: str,
    nested_list_fn_name: str
) -> Union[mlList[Int], Matrix[Int]]:
    if is_matrix_type(vec_or_nested_list.type):
        cur = call(vec_fn_name, mlList[Int], scalar, vec_or_nested_list[0])
        recursed = call(nested_list_fn_name, Matrix[Int], scalar, vec_or_nested_list[1:])
        general_answer = recursed.prepend(cur)
        return ite(
            or_objects(vec_or_nested_list.len() < 1),
            Matrix.empty(Int),
            general_answer
        )
    elif is_list_type(vec_or_nested_list.type) and is_primitive_type(get_list_element_type(vec_or_nested_list.type)):
        cur = compute_fn(scalar, vec_or_nested_list[0])
        recursed = call(vec_fn_name, mlList[Int], scalar, vec_or_nested_list[1:])
        general_answer = recursed.prepend(cur)
        return ite(
            or_objects(vec_or_nested_list.len() < 1),
            mlList.empty(Int),
            general_answer
        )
    raise Exception("Unsupported types for scalar operations!")

def map_body(
    vec_or_nested_list: Union[mlList[Int], Matrix[Int]],
    map_fn: Callable[[Int], Int],
    vec_map_fn_name: str,
    nested_list_map_fn_name: str
) -> Union[mlList[Int], Matrix[Int]]:
    if is_matrix_type(vec_or_nested_list.type):
        cur = call(vec_map_fn_name, mlList[Int], vec_or_nested_list[0])
        recursed = call(nested_list_map_fn_name, Matrix[Int], vec_or_nested_list[1:])
        general_answer = recursed.prepend(cur)
        return ite(
            or_objects(vec_or_nested_list.len() < 1),
            Matrix.empty(Int),
            general_answer
        )
    elif is_list_type(vec_or_nested_list.type) and is_primitive_type(get_list_element_type(vec_or_nested_list.type)):
        cur = map_fn(vec_or_nested_list[0])
        recursed = call(vec_map_fn_name, mlList[Int], vec_or_nested_list[1:])
        general_answer = recursed.prepend(cur)
        return ite(
            or_objects(vec_or_nested_list.len() < 1),
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
        nested_list_fn_name=NESTED_LIST_ELEMWISE_ADD
    ),
    x,
    y
)
nested_list_elemwise_add = fn_decl_recursive(
    NESTED_LIST_ELEMWISE_ADD,
    Matrix[Int],
    elemwise_body(
        left=nested_x,
        right=nested_y,
        compute_fn=lambda int_x, int_y: int_x + int_y,
        vec_fn_name=VEC_ELEMWISE_ADD,
        nested_list_fn_name=NESTED_LIST_ELEMWISE_ADD
    ),
    nested_x,
    nested_y
)

vec_elemwise_sub = fn_decl_recursive(
    VEC_ELEMWISE_SUB,
    mlList[Int],
    elemwise_body(
        left=x,
        right=y,
        compute_fn=lambda int_x, int_y: int_x - int_y,
        vec_fn_name=VEC_ELEMWISE_SUB,
        nested_list_fn_name=NESTED_LIST_ELEMWISE_SUB
    ),
    x,
    y
)
nested_list_elemwise_sub = fn_decl_recursive(
    NESTED_LIST_ELEMWISE_SUB,
    Matrix[Int],
    elemwise_body(
        left=nested_x,
        right=nested_y,
        compute_fn=lambda int_x, int_y: int_x + int_y,
        vec_fn_name=VEC_ELEMWISE_SUB,
        nested_list_fn_name=NESTED_LIST_ELEMWISE_SUB
    ),
    nested_x,
    nested_y
)

vec_elemwise_mul = fn_decl_recursive(
    VEC_ELEMWISE_MUL,
    mlList[Int],
    elemwise_body(
        left=x,
        right=y,
        compute_fn=lambda int_x, int_y: int_x * int_y,
        vec_fn_name=VEC_ELEMWISE_MUL,
        nested_list_fn_name=NESTED_LIST_ELEMWISE_MUL
    ),
    x,
    y
)
nested_list_elemwise_mul = fn_decl_recursive(
    NESTED_LIST_ELEMWISE_MUL,
    Matrix[Int],
    elemwise_body(
        left=nested_x,
        right=nested_y,
        compute_fn=lambda int_x, int_y: int_x * int_y,
        vec_fn_name=VEC_ELEMWISE_MUL,
        nested_list_fn_name=NESTED_LIST_ELEMWISE_MUL
    ),
    nested_x,
    nested_y
)

vec_elemwise_div = fn_decl_recursive(
    VEC_ELEMWISE_DIV,
    mlList[Int],
    elemwise_body(
        left=x,
        right=y,
        compute_fn=lambda int_x, int_y: int_x // int_y,
        vec_fn_name=VEC_ELEMWISE_DIV,
        nested_list_fn_name=NESTED_LIST_ELEMWISE_DIV
    ),
    x,
    y
)
nested_list_elemwise_div = fn_decl_recursive(
    NESTED_LIST_ELEMWISE_DIV,
    Matrix[Int],
    elemwise_body(
        left=nested_x,
        right=nested_y,
        compute_fn=lambda int_x, int_y: int_x // int_y,
        vec_fn_name=VEC_ELEMWISE_DIV,
        nested_list_fn_name=NESTED_LIST_ELEMWISE_DIV
    ),
    nested_x,
    nested_y
)

vec_scalar_add = fn_decl_recursive(
    VEC_SCALAR_ADD,
    mlList[Int],
    scalar_body(
        scalar=a,
        vec_or_nested_list=x,
        compute_fn=lambda scalar, int_x: scalar + int_x,
        vec_fn_name=VEC_SCALAR_ADD,
        nested_list_fn_name=NESTED_LIST_SCALAR_ADD
    ),
    a,
    x
)
nested_list_scalar_add = fn_decl_recursive(
    NESTED_LIST_SCALAR_ADD,
    mlList[Int],
    scalar_body(
        scalar=a,
        vec_or_nested_list=nested_x,
        compute_fn=lambda scalar, int_x: scalar + int_x,
        vec_fn_name=VEC_SCALAR_ADD,
        nested_list_fn_name=NESTED_LIST_SCALAR_ADD
    ),
    a,
    nested_x
)

vec_scalar_mul = fn_decl_recursive(
    VEC_SCALAR_MUL,
    mlList[Int],
    scalar_body(
        scalar=a,
        vec_or_nested_list=x,
        compute_fn=lambda scalar, int_x: scalar * int_x,
        vec_fn_name=VEC_SCALAR_MUL,
        nested_list_fn_name=NESTED_LIST_SCALAR_MUL
    ),
    a,
    x
)
nested_list_scalar_mul = fn_decl_recursive(
    NESTED_LIST_SCALAR_MUL,
    mlList[Int],
    scalar_body(
        scalar=a,
        vec_or_nested_list=nested_x,
        compute_fn=lambda scalar, int_x: scalar * int_x,
        vec_fn_name=VEC_SCALAR_MUL,
        nested_list_fn_name=NESTED_LIST_SCALAR_MUL
    ),
    a,
    nested_x
)

vec_scalar_div = fn_decl_recursive(
    VEC_SCALAR_DIV,
    mlList[Int],
    scalar_body(
        scalar=a,
        vec_or_nested_list=x,
        compute_fn=lambda scalar, int_x: int_x // scalar,
        vec_fn_name=VEC_SCALAR_DIV,
        nested_list_fn_name=NESTED_LIST_SCALAR_DIV
    ),
    a,
    x
)
nested_list_scalar_div = fn_decl_recursive(
    NESTED_LIST_SCALAR_DIV,
    mlList[Int],
    scalar_body(
        scalar=a,
        vec_or_nested_list=nested_x,
        compute_fn=lambda scalar, int_x: int_x // scalar,
        vec_fn_name=VEC_SCALAR_DIV,
        nested_list_fn_name=NESTED_LIST_SCALAR_DIV
    ),
    a,
    nested_x
)

vec_scalar_sub = fn_decl_recursive(
    VEC_SCALAR_SUB,
    mlList[Int],
    scalar_body(
        scalar=a,
        vec_or_nested_list=x,
        compute_fn=lambda scalar, int_x: int_x - scalar,
        vec_fn_name=VEC_SCALAR_SUB,
        nested_list_fn_name=NESTED_LIST_SCALAR_SUB
    ),
    a,
    x
)
nested_list_scalar_sub = fn_decl_recursive(
    NESTED_LIST_SCALAR_SUB,
    mlList[Int],
    scalar_body(
        scalar=a,
        vec_or_nested_list=nested_x,
        compute_fn=lambda scalar, int_x: int_x - scalar,
        vec_fn_name=VEC_SCALAR_SUB,
        nested_list_fn_name=NESTED_LIST_SCALAR_SUB
    ),
    a,
    nested_x
)


def get_nested_list_computation_ps_grammar_fn(
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
    def nested_list_computation_ps_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
        ret_val = writes[0]
        base, active = reads
        if not fixed_grammar:
            return ret_val == nested_list_computation(
                args=[base, active],
                constants=constants,
                compute_ops=compute_ops,
                depth=depth
            )
        else:
            return ret_val == fixed_out_fn(base, active)
    return nested_list_computation_ps_grammar_fn

def get_matrix_computation_hole_inv0_grammar(
    constants: List[Int],
    hole_body: Callable[[List[MatrixOrVecT], List[Int]], MatrixOrVecT]
) -> InvGrammar:
    def inv0_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
        # outer loop grammar
        out, col, pixel, row, row_vec = writes
        base, active = reads
        index_lower_bound = choose(Int(0), Int(1))
        index_upper_bound = choose(base.len(), base[0].len())
        matrix_choices = [
            base[:row],
            base[:col],
            active[:row],
            active[:col],
        ]
        return and_objects(
            row >= index_lower_bound,
            row <= index_upper_bound,
            out == hole_body(matrix_choices, constants)
        )
    return InvGrammar(inv0_grammar_fn, [])

def get_matrix_computation_hole_inv1_grammar(
    constants: List[Int],
    hole_body: Callable[[List[MatrixOrVecT], List[Int]], MatrixOrVecT]
) -> InvGrammar:
    def inv1_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
        # inner loop grammar
        col, pixel, row_vec = writes
        out, row = in_scope
        base, active = reads
        index_lower_bound = choose(Int(0), Int(1))
        index_upper_bound = choose(base.len(), base[0].len())
        vec_choices = [base[row][:col], active[row][:col]]
        matrix_choices = [base[:row], active[:row], base[:col], active[:col]]
        return and_objects(
            row >= index_lower_bound,
            row < index_upper_bound,
            col >= index_lower_bound,
            col <= index_upper_bound,
            row_vec == hole_body(vec_choices, constants),
            out == hole_body(matrix_choices, constants)
        )
    return InvGrammar(inv1_grammar_fn, ["row", "agg.result"])

def get_matrix_computation_hole_ps_grammar(
    constants: List[Int],
    hole_body: Callable[[List[MatrixOrVecT], List[Int]], MatrixOrVecT]
) -> InvGrammar:
    def ps_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
        ret_val = writes[0]
        base, active = reads
        return ret_val == hole_body([base, active], constants)
    return ps_grammar_fn


def get_nested_list_computation_inv0_grammar(
    fixed_grammar: bool,
    fixed_out_fn: Optional[Any] = None, # TODO(jie): add type for this
    constants: Optional[List[Int]] = None,
    compute_ops: Optional[List[str]] = None,
    depth: Optional[int] = None,
) -> InvGrammar:
    if fixed_grammar:
        if fixed_out_fn is None:
            raise Exception("Must pass in an override out!")
    def nested_list_computation_inv0_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
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
            nested_list_choices = [
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
                out == nested_list_computation(
                    args=nested_list_choices,
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
    return InvGrammar(nested_list_computation_inv0_grammar_fn, [])

def get_nested_list_computation_inv1_grammar(
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
    def nested_list_computation_inv1_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
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
            nested_list_choices = [
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
                out == nested_list_computation(
                    args=nested_list_choices,
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
        nested_list_computation_inv1_grammar_fn,
        ["row", "agg.result"]
    )

def get_nested_list_computation_with_counts_ps_grammar_fn(
    fixed_grammar: bool,
    fixed_out_fn: Optional[Any] = None, # TODO(jie): add type for this
    constants: Optional[List[Int]] = None,
    ordered_compute_ops: Optional[OrderedDict] = None,
    depth: Optional[int] = None,
) -> Callable[[List[Object], List[Object], List[Object]], Bool]:
    if fixed_grammar and fixed_out_fn is None:
        raise Exception("Must pass in an override out!")
    def nested_list_computation_ps_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
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
    return nested_list_computation_ps_grammar_fn

def get_nested_list_computation_with_counts_inv0_grammar(
    fixed_grammar: bool,
    fixed_out_fn: Optional[Any] = None, # TODO(jie): add type for this
    constants: Optional[List[Int]] = None,
    ordered_compute_ops: Optional[OrderedDict] = None,
    depth: Optional[int] = None,
) -> InvGrammar:
    if fixed_grammar:
        if fixed_out_fn is None:
            raise Exception("Must pass in an override out!")
    def nested_list_computation_inv0_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
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
            nested_list_choices = [
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
                    args=nested_list_choices,
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
    return InvGrammar(nested_list_computation_inv0_grammar_fn, [])

def get_nested_list_computation_with_counts_inv1_grammar(
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
    def nested_list_computation_inv1_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
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
            nested_list_choices = [
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
                    args=nested_list_choices,
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
        nested_list_computation_inv1_grammar_fn,
        ["row", "agg.result"]
    )

def nested_list_computation_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        vec_elemwise_add,
        nested_list_elemwise_add,
        vec_elemwise_sub,
        nested_list_elemwise_sub,
        vec_elemwise_mul,
        nested_list_elemwise_mul,
        vec_elemwise_div,
        nested_list_elemwise_div,
        vec_scalar_add,
        nested_list_scalar_add,
        vec_scalar_sub,
        nested_list_scalar_sub,
        vec_scalar_mul,
        nested_list_scalar_mul,
        vec_scalar_div,
        nested_list_scalar_div
    ]

def get_nested_list_computation_grammars_without_analysis(depth: int) -> Tuple[InvGrammar, InvGrammar, Callable[[List[Object], List[Object], List[Object]], Bool]]:
    return get_nested_list_computation_grammars(
        fixed_grammar=False,
        constants=[Int(0), Int(2), Int(128), Int(32)],
        compute_ops=["+", "-", "*", "//"],
        depth=depth
    )

def get_nested_list_computation_grammars(
    fixed_grammar: bool,
    fixed_row_vec_fn: Optional[Any] = None, # TODO(jie): add type for this
    fixed_out_fn: Optional[Any] = None, # TODO(jie): add type for this
    constants: Optional[List[Int]] = None,
    compute_ops: Optional[List[str]] = None,
    depth: Optional[int] = None,
) -> Tuple[InvGrammar, InvGrammar, Callable[[List[Object], List[Object], List[Object]], Bool]]:
    inv0_grammar = get_nested_list_computation_inv0_grammar(
            fixed_grammar=fixed_grammar,
            fixed_out_fn=fixed_out_fn,
            constants=constants,
            compute_ops=compute_ops,
            depth=depth
        )
    inv1_grammar = get_nested_list_computation_inv1_grammar(
        fixed_grammar=fixed_grammar,
        fixed_row_vec_fn=fixed_row_vec_fn,
        fixed_out_fn=fixed_out_fn,
        constants=constants,
        ordered_compute_ops=compute_ops,
        depth=depth
    )
    ps_grammar = get_nested_list_computation_ps_grammar_fn(
        fixed_grammar=fixed_grammar,
        fixed_out_fn=fixed_out_fn,
        constants=constants,
        compute_ops=compute_ops,
        depth=depth
    )
    return inv0_grammar, inv1_grammar, ps_grammar

# Uninterpreted functions
exp = fn_decl(TEST_EXP_FN_NAME, Int, None, int_x)
vec_exp_map = fn_decl_recursive(
    VEC_MAP_TEST_EXP_FN_NAME,
    mlList[Int],
    map_body(
        vec_or_nested_list=x,
        map_fn=lambda int_x: call_exp(int_x),
        vec_map_fn_name=VEC_MAP_TEST_EXP_FN_NAME,
        nested_list_map_fn_name=NESTED_LIST_MAP_TEST_EXP_FN_NAME
    ),
    x
)
nested_list_exp_map = fn_decl_recursive(
    NESTED_LIST_MAP_TEST_EXP_FN_NAME,
    mlList[Int],
    map_body(
        vec_or_nested_list=nested_x,
        map_fn=lambda int_x: call_exp(int_x),
        vec_map_fn_name=VEC_MAP_TEST_EXP_FN_NAME,
        nested_list_map_fn_name=NESTED_LIST_MAP_TEST_EXP_FN_NAME
    ),
    nested_x
)

uninterp_div = fn_decl(UNINTERP_DIV_FN_NAME, Int, None, int_x, int_y)