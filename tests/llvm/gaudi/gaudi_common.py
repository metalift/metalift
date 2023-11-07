import typing
from typing import List

from metalift.ir import (FnObject, IntObject, ListObject, NewObject, Synth,
                         call, call_value, choose, fn_decl, fn_decl_recursive,
                         ite)

VECTORADD = "vector_add"
ELEMWISEMUL = "elemwise_mul"
SCALARMUL = "scalar_mul"
BROADCASTADD = "broadcast_add"
REDUCESUM = "reduce_sum"
REDUCEMUL = "reduce_mul"
SELECT = "select"
SELECTION = "selection"
NESTEDSELECTION = "nested_selection"


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

def call_selection(
    left: ListObject[IntObject],
    right: ListObject[IntObject],
    select_fn: FnObject[typing.Tuple[IntObject, IntObject, IntObject]]
) -> ListObject[IntObject]:
    return call(SELECTION, ListObject[IntObject], left, right, select_fn)

def call_nested_selection(
    left: ListObject[ListObject[IntObject]],
    right: ListObject[ListObject[IntObject]],
    select_fn: FnObject[typing.Tuple[IntObject, IntObject, IntObject]]
) -> ListObject[ListObject[IntObject]]:
    return call(NESTEDSELECTION, ListObject[ListObject[IntObject]], left, right, select_fn)

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
int_x = IntObject("x")
int_y = IntObject("y")

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

# Selection criteria
select_min_body = ite(int_x < int_y, int_x, int_y)
select_linear_burn_body = int_x + int_y - 255
select_mul8x8_div255_body = (int_x * int_y) // 255
select_screen8x8_body = int_x + int_y - select_mul8x8_div255_body


select_fn_obj = FnObject((IntObject, IntObject, IntObject), SELECT)
select_fn_decl = fn_decl(SELECT, IntObject, None, int_x, int_y)

def get_select_synth(*select_bodies: NewObject) -> Synth:
    return Synth(
        SELECT,
        choose(*select_bodies).src,
        int_x.src,
        int_y.src
    )

def selection_body(
    left: ListObject[IntObject],
    right: ListObject[IntObject],
    select_fn: FnObject[typing.Tuple[IntObject, IntObject, IntObject]]
) -> ListObject[IntObject]:
    vec_size = left.len()
    cur = call_value(select_fn, left[0], right[0])
    left_rest = left[1:]
    right_rest = right[1:]
    recursed = call_selection(left_rest, right_rest, select_fn)
    general_answer = recursed.prepend(cur)
    return ite(vec_size < 1, ListObject.empty(IntObject), general_answer)

selection = fn_decl_recursive(
    SELECTION,
    ListObject[IntObject],
    selection_body(x, y, select_fn_obj),
    x,
    y,
    select_fn_obj
)

def nested_selection_body(
    left: ListObject[ListObject[IntObject]],
    right: ListObject[ListObject[IntObject]],
    select_fn: FnObject[typing.Tuple[IntObject, IntObject, IntObject]]
) -> ListObject[ListObject[IntObject]]:
    vec_size = left.len()
    cur = call_selection(left[0], right[0], select_fn)
    recursed = call_nested_selection(left[1:], right[1:], select_fn)
    general_answer = recursed.prepend(cur)
    return ite(vec_size < 1, ListObject.empty(ListObject[IntObject]), general_answer)
nested_selection = fn_decl_recursive(
    NESTEDSELECTION,
    ListObject[ListObject[IntObject]],
    nested_selection_body(nested_x, nested_y, select_fn_obj),
    nested_x,
    nested_y,
    select_fn_obj
)