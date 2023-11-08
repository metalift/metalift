import typing
from typing import List, Union
from metalift.frontend.llvm import InvGrammar

from metalift.ir import (Fn, Int, List as mlList, Object, Synth,
                         call, call_value, choose, fn_decl, fn_decl_recursive,
                         ite)
from metalift.vc_util import and_objects, or_objects

VECTORADD = "vector_add"
ELEMWISEMUL = "elemwise_mul"
SCALARMUL = "scalar_mul"
BROADCASTADD = "broadcast_add"
REDUCESUM = "reduce_sum"
REDUCEMUL = "reduce_mul"
SELECT_TWO_ARGS = "select_two_args"
SELECTION_TWO_ARGS = "selection_two_args"
NESTED_SELECTION_TWO_ARGS = "nested_selection_two_args"


def call_vector_add(left: mlList[Int], right: mlList[Int]) -> mlList[Int]:
    return call(VECTORADD, mlList[Int], left, right)

def call_scalar_mul(left: mlList[Int], right: mlList[Int]) -> mlList[Int]:
    return call(SCALARMUL, mlList[Int], left, right)

def call_broadcast_add(left: mlList[Int], right: mlList[Int]) -> mlList[Int]:
    return call(BROADCASTADD, mlList[Int], left, right)

def call_reduce_sum(lst) -> Int:
    return call(REDUCESUM, Int, lst)

def call_reduce_mul(lst) -> Int:
    return call(REDUCEMUL, Int, lst)

def call_elemwise_mul(left: mlList[Int], right: mlList[Int]) -> mlList[Int]:
    return call(ELEMWISEMUL, mlList[Int], left, right)

def call_selection(
    left: mlList[Int],
    right: mlList[Int],
    select_fn: Fn[typing.Tuple[Int, Int, Int]]
) -> mlList[Int]:
    return call(SELECTION, mlList[Int], left, right, select_fn)

def call_nested_selection(
    left: mlList[mlList[Int]],
    right: mlList[mlList[Int]],
    select_fn: Fn[typing.Tuple[Int, Int, Int]]
) -> mlList[mlList[Int]]:
    return call(NESTEDSELECTION, mlList[mlList[Int]], left, right, select_fn)

an_arr2_to_arr = lambda left, right: choose(
    call_elemwise_mul(left, right),
    call_vector_add(left, right),
)
an_int_and_arr_to_arr = lambda num, arr: choose(
    call_scalar_mul(num, arr),
    call_broadcast_add(num, arr),
)
an_arr_to_int = lambda arr: choose(
    call_reduce_sum(arr),
    call_reduce_mul(arr),
)

# Define some common objects
a = Int("a")
x = mlList(Int, "x")
y = mlList(Int, "y")
nested_x = mlList(mlList[Int], "nested_x")
nested_y = mlList(mlList[Int], "nested_y")
int_x = Int("x")
int_y = Int("y")

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

def elemwise_mul_body(left: mlList[Int], right: mlList[Int]) -> mlList[Int]:
    vec_size = left.len()
    cur = left[0] * right[0]
    left_rest = left[1:]
    right_rest = right[1:]
    recursed = call_elemwise_mul(left_rest, right_rest)
    general_answer = recursed.prepend(cur)
    return ite(vec_size < 1, mlList.empty(Int), general_answer)
elemwise_mul = fn_decl_recursive(ELEMWISEMUL, mlList[Int], elemwise_mul_body(x, y), x, y)

# Helper functions for selections
def mul8x8_div255_body(int_x: IntObject, int_y: IntObject) -> IntObject:
    return (int_x * int_y) // 255

def screen8x8_body(int_x: IntObject, int_y: IntObject) -> IntObject:
    return int_x + int_y - mul8x8_div255_body(int_x, int_y)

# Selection criteria
def select_darken_blend_body(int_x: IntObject, int_y: IntObject) -> IntObject:
    return ite(int_x > int_y, int_y, int_x)

def select_multiply_blend_body(int_x: IntObject, int_y: IntObject) -> IntObject:
    return mul8x8_div255_body(int_x, int_y)

select_fn_obj = Fn((Int, Int, Int), SELECT)
select_fn_decl = fn_decl(SELECT, Int, None, int_x, int_y)

def get_select_synth(*select_bodies: Object) -> Synth:
    return Synth(
        SELECT,
        choose(*select_bodies).src,
        int_x.src,
        int_y.src
    )

def selection_body(
    left: mlList[Int],
    right: mlList[Int],
    select_fn: Fn[typing.Tuple[Int, Int, Int]]
) -> mlList[Int]:
    vec_size = left.len()
    cur = call_value(select_fn, left[0], right[0])
    recursed = call_selection_two_args(left[1:], right[1:], select_fn)
    general_answer = recursed.prepend(cur)
    return ite(vec_size < 1, mlList.empty(Int), general_answer)

selection = fn_decl_recursive(
    SELECTION,
    mlList[Int],
    selection_body(x, y, select_fn_obj),
    x,
    y,
    select_fn_obj
)

def nested_selection_body(
    left: mlList[mlList[Int]],
    right: mlList[mlList[Int]],
    select_fn: Fn[typing.Tuple[Int, Int, Int]]
) -> mlList[mlList[Int]]:
    vec_size = left.len()
    cur = call_selection(left[0], right[0], select_fn)
    recursed = call_nested_selection(left[1:], right[1:], select_fn)
    general_answer = recursed.prepend(cur)
    return ite(vec_size < 1, mlList.empty(mlList[Int]), general_answer)
nested_selection = fn_decl_recursive(
    NESTEDSELECTION,
    mlList[mlList[Int]],
    nested_selection_body(nested_x, nested_y, select_fn_obj),
    nested_x,
    nested_y,
    select_two_args_fn_obj
)

all_possible_select_two_args_bodies = [
    select_multiply_blend_body(int_x, int_y),
    select_linear_burn_body(int_x, int_y),
    select_color_burn_body(int_x, int_y),
    select_lighten_blend_body(int_x, int_y),
    select_screen_blend_body(int_x, int_y),
    select_linear_dodge_body(int_x, int_y),
    select_color_dodge_body(int_x, int_y),
    select_overlay_blend_body(int_x, int_y),
    select_darken_blend_body(int_x, int_y)
]
all_possible_selects_two_args_synth = get_select_two_args_synth(all_possible_select_two_args_bodies, [int_x, int_y])
selection_two_args_synth = get_selection_two_args_synth(x, y, select_two_args_fn_obj)

def selection_two_args_ps_grammar_fn(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> BoolObject:
    ret_val = writes[0]
    base, active = reads
    base_or_active = choose(base, active)
    return ret_val == call_nested_selection_two_args(base_or_active, base_or_active, select_two_args_fn_obj)

def selection_two_args_inv0_grammar_fn(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> BoolObject:
    # outer loop grammar
    out, col, pixel, row, row_vec = writes
    base, active = reads
    index_lower_bound = choose(1 - IntObject(0), IntObject(0), IntObject(1))
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
    nested_list = choose(
        base,
        base[:row],
        base[:col],
        active,
        active[:row],
        active[:col],
    )
    return and_objects(
        index_lower_cond,
        index_upper_cond,
        out == call_nested_selection_two_args(nested_list, nested_list, select_two_args_fn_obj)
    )

def selection_two_args_inv1_grammar_fn(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> BoolObject:
    # inner loop grammar
    col, pixel, row_vec = writes
    out, row = in_scope
    base, active = reads
    index_lower_bound = choose(1 - IntObject(0), IntObject(0), IntObject(1))
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
    vec = choose(
        base[0][:col],
        base[row][:col],
        base[col][:row],
        base[0][:row],
        active[0][:col],
        active[row][:col],
        active[col][:row],
        active[0][:row],
        row_vec
    )
    nested_list = choose(
        base,
        base[:row],
        base[:col],
        active,
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
    return [select_two_args_fn_decl, selection_two_args_fn_decl, nested_selection_two_args_fn_decl]

selection_two_args_inv0_grammar = InvGrammar(selection_two_args_inv0_grammar_fn, [])
selection_two_args_inv1_grammar = InvGrammar(selection_two_args_inv1_grammar_fn, ["row", "agg.result"])