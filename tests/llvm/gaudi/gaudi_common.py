import typing
from typing import List, Union
from metalift.frontend.llvm import InvGrammar

from metalift.ir import (BoolObject, FnDecl, FnDeclRecursive, FnObject, IntObject, ListObject, NewObject, Synth,
                         call, call_value, choose, fn_decl, fn_decl_recursive, get_object_exprs,
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


def call_vector_add(left: ListObject[IntObject], right: ListObject[IntObject]) -> ListObject[IntObject]:
    return call(VECTORADD, ListObject[IntObject], left, right)

def call_scalar_mul(left: ListObject[IntObject], right: ListObject[IntObject]) -> ListObject[IntObject]:
    return call(SCALARMUL, ListObject[IntObject], left, right)

def call_broadcast_add(left: ListObject[IntObject], right: ListObject[IntObject]) -> ListObject[IntObject]:
    return call(BROADCASTADD, ListObject[IntObject], left, right)

def call_reduce_sum(lst) -> IntObject:
    return call(REDUCESUM, IntObject, lst)

def call_reduce_mul(lst) -> IntObject:
    return call(REDUCEMUL, IntObject, lst)

def call_elemwise_mul(left: ListObject[IntObject], right: ListObject[IntObject]) -> ListObject[IntObject]:
    return call(ELEMWISEMUL, ListObject[IntObject], left, right)

def call_selection_two_args(
    left: ListObject[IntObject],
    right: ListObject[IntObject],
    select_fn: FnObject[typing.Tuple[IntObject, IntObject, IntObject]]
) -> ListObject[IntObject]:
    return call(SELECTION_TWO_ARGS, ListObject[IntObject], left, right, select_fn)

def call_nested_selection_two_args(
    left: ListObject[ListObject[IntObject]],
    right: ListObject[ListObject[IntObject]],
    select_fn: FnObject[typing.Tuple[IntObject, IntObject, IntObject]]
) -> ListObject[ListObject[IntObject]]:
    return call(NESTED_SELECTION_TWO_ARGS, ListObject[ListObject[IntObject]], left, right, select_fn)

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
a = IntObject("a")
x = ListObject(IntObject, "x")
y = ListObject(IntObject, "y")
nested_x = ListObject(ListObject[IntObject], "nested_x")
nested_y = ListObject(ListObject[IntObject], "nested_y")
int_x = IntObject("int_x")
int_y = IntObject("int_y")

def vector_add_body(left: ListObject[IntObject], right: ListObject[IntObject]) -> ListObject[IntObject]:
    vec_size = left.len()
    cur = left[0] + right[0]
    left_rest = left[1:]
    right_rest = right[1:]
    recursed = call_vector_add(left_rest, right_rest)
    general_answer = recursed.prepend(cur)
    return ite(vec_size < 1, ListObject.empty(IntObject), general_answer)
vector_add = fn_decl_recursive(VECTORADD, ListObject[IntObject], vector_add_body(x, y), x, y)

def scalar_mul_body(scalar: IntObject, arr: ListObject[IntObject]) -> ListObject[IntObject]:
    vec_size = arr.len()
    cur = scalar * arr[0]
    arr_rest = arr[1:]
    recursed = call_scalar_mul(scalar, arr_rest)
    general_answer = recursed.prepend(cur)
    return ite(vec_size < 1, ListObject.empty(IntObject), general_answer)
scalar_mul = fn_decl_recursive(SCALARMUL, ListObject[IntObject], scalar_mul_body(a, x), a, x)

def broadcast_add_body(scalar: IntObject, arr: ListObject[IntObject]) -> ListObject[IntObject]:
    vec_size = arr.len()
    cur = scalar + arr[0]
    arr_rest = arr[1:]
    recursed = call_broadcast_add(scalar, arr_rest)
    general_answer = recursed.prepend(cur)
    return ite(vec_size < 1, ListObject.empty(IntObject), general_answer)
broadcast_add = fn_decl_recursive(BROADCASTADD, ListObject[IntObject], broadcast_add_body(a, x), a, x)

def reduce_sum_body(lst: List[IntObject]) -> IntObject:
    vec_size = lst.len()
    cur = lst[0]
    lst_rest = lst[1:]
    recursed = call_reduce_sum(lst_rest)
    general_answer = cur + recursed
    return ite(vec_size < 1, IntObject(0), general_answer)
reduce_sum = fn_decl_recursive(REDUCESUM, IntObject, reduce_sum_body(x), x)

def reduce_mul_body(lst: ListObject[IntObject]) -> IntObject:
    vec_size = lst.len()
    cur = lst[0]
    lst_rest = lst[1:]
    recursed = call_reduce_mul(lst_rest)
    general_answer = cur * recursed
    return ite(vec_size < 1, IntObject(1), general_answer)
reduce_mul = fn_decl_recursive(REDUCEMUL, IntObject, reduce_mul_body(x), x)

def elemwise_mul_body(left: ListObject[IntObject], right: ListObject[IntObject]) -> ListObject[IntObject]:
    vec_size = left.len()
    cur = left[0] * right[0]
    left_rest = left[1:]
    right_rest = right[1:]
    recursed = call_elemwise_mul(left_rest, right_rest)
    general_answer = recursed.prepend(cur)
    return ite(vec_size < 1, ListObject.empty(IntObject), general_answer)
elemwise_mul = fn_decl_recursive(ELEMWISEMUL, ListObject[IntObject], elemwise_mul_body(x, y), x, y)

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

def select_linear_burn_body(int_x: IntObject, int_y: IntObject) -> IntObject:
    return int_x + int_y - 255

def select_color_burn_body(int_x: IntObject, int_y: IntObject) -> IntObject:
    return ite(
        int_x == 0,
        IntObject(255),
        255 - (255 - int_x // int_y)
    )

def select_lighten_blend_body(int_x: IntObject, int_y: IntObject) -> IntObject:
    return ite(int_x < int_y, int_y, int_x)

def select_screen_blend_body(int_x: IntObject, int_y: IntObject) -> IntObject:
    return screen8x8_body(int_x, int_y)

def select_linear_dodge_body(int_x: IntObject, int_y: IntObject) -> IntObject:
    return int_x + int_y

def select_color_dodge_body(int_x: IntObject, int_y: IntObject) -> IntObject:
    return ite(
        int_y == 255,
        IntObject(255),
        int_x // (255 - int_y)
    )

def select_overlay_blend_body(int_x: IntObject, int_y: IntObject) -> IntObject:
    return ite(
        int_x >= 128,
        screen8x8_body(2 * int_x, int_x) - 255,
        mul8x8_div255_body(2 * int_x, int_x)
    )

select_two_args_fn_obj = FnObject((IntObject, IntObject, IntObject), SELECT_TWO_ARGS)
select_two_args_fn_decl = fn_decl(SELECT_TWO_ARGS, IntObject, None, int_x, int_y)
selection_two_args_fn_decl = fn_decl(SELECTION_TWO_ARGS, ListObject[IntObject], None, x, y, select_two_args_fn_obj)

def get_select_two_args_synth(select_bodies: List[NewObject], args: List[NewObject]) -> Synth:
    return Synth(
        SELECT_TWO_ARGS,
        choose(*select_bodies).src,
        *get_object_exprs(*args)
    )

def selection_two_args_body(
    left: ListObject[IntObject],
    right: ListObject[IntObject],
    select_fn: FnObject[typing.Tuple[IntObject, IntObject, IntObject]]
) -> ListObject[IntObject]:
    cur = call_value(select_fn, left[0], right[0])
    recursed = call_selection_two_args(left[1:], right[1:], select_fn)
    general_answer = recursed.prepend(cur)
    return ite(
        or_objects(left.len() < 1, left.len() != right.len()),
        ListObject.empty(IntObject),
        general_answer
    )

def get_selection_two_args_synth(
    left: ListObject[IntObject],
    right: ListObject[IntObject],
    select_fn: FnObject[typing.Tuple[IntObject, IntObject, IntObject]]
) -> Synth:
    return Synth(
        SELECTION_TWO_ARGS,
        selection_two_args_body(left, right, select_fn).src,
        left.src,
        right.src,
        select_fn.src
    )

def nested_selection_two_args_body(
    left: ListObject[ListObject[IntObject]],
    right: ListObject[ListObject[IntObject]],
    select_fn: FnObject[typing.Tuple[IntObject, IntObject, IntObject]]
) -> ListObject[ListObject[IntObject]]:
    cur = call_selection_two_args(left[0], right[0], select_fn)
    recursed = call_nested_selection_two_args(left[1:], right[1:], select_fn)
    general_answer = recursed.prepend(cur)
    return ite(
        or_objects(left.len() < 1, left.len() != right.len()),
        ListObject.empty(ListObject[IntObject]),
        general_answer
    )
nested_selection_two_args_fn_decl = fn_decl_recursive(
    NESTED_SELECTION_TWO_ARGS,
    ListObject[ListObject[IntObject]],
    nested_selection_two_args_body(nested_x, nested_y, select_two_args_fn_obj),
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