from typing import List

from metalift.ir import (Choose, FnDecl, IntObject, ListObject, call, choose, choose_fn_decl_and_call, fn_decl, fn_decl_recursive,
                         ite)

VECTORADD = "vector_add"
ELEMWISEMUL = "elemwise_mul"
SCALARMUL = "scalar_mul"
BROADCASTADD = "broadcast_add"
REDUCESUM = "reduce_sum"
REDUCEMUL = "reduce_mul"
ELEMWISEMIN = "elemwise_min"
NESTEDELEMWISEMIN = "nested_elemwise_min"
SELECTMIN = "select_min"


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

def call_elemwise_min(left: ListObject[IntObject], right: ListObject[IntObject]) -> ListObject[IntObject]:
    return call(ELEMWISEMIN, ListObject[IntObject], left, right)

def call_nested_elemwise_min(
    left: ListObject[ListObject[IntObject]],
    right: ListObject[ListObject[IntObject]]
) -> ListObject[ListObject[IntObject]]:
    return call(NESTEDELEMWISEMIN, ListObject[ListObject[IntObject]], left, right)

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

def elemwise_min_body(left: ListObject[IntObject], right: ListObject[IntObject]) -> ListObject[IntObject]:
    vec_size = left.len()
    cur = ite(left[0] < right[0], left[0], right[0])
    left_rest = left[1:]
    right_rest = right[1:]
    recursed = call_elemwise_min(left_rest, right_rest)
    general_answer = recursed.prepend(cur)
    return ite(vec_size < 1, ListObject.empty(IntObject), general_answer)
elemwise_min = fn_decl_recursive(ELEMWISEMIN, ListObject[IntObject], elemwise_min_body(x, y), x, y)

def nested_elemwise_min_body(
    left: ListObject[ListObject[IntObject]],
    right: ListObject[ListObject[IntObject]]
) -> ListObject[ListObject[IntObject]]:
    vec_size = left.len()
    cur = call_elemwise_min(left[0], right[0])
    recursed = call_nested_elemwise_min(left[1:], right[1:])
    general_answer = recursed.prepend(cur)
    return ite(vec_size < 1, ListObject.empty(ListObject[IntObject]), general_answer)
nested_elemwise_min = fn_decl_recursive(
    NESTEDELEMWISEMIN,
    ListObject[ListObject[IntObject]],
    nested_elemwise_min_body(nested_x, nested_y),
    nested_x,
    nested_y
)

# # Selection criteria
# select_max = fn_decl(
#     SELECTMIN,
#     IntObject,
#     ite(int_x < int_y, x, y),
#     x,
#     y
# )
# selection = Choose(select_max)
# def selection_body(
#     left: ListObject[IntObject],
#     right: ListObject[IntObject],
#     select_fns: List[FnDecl]
# ) -> ListObject[IntObject]:
#     vec_size = left.len()
#     cur = choose_fn_decl_and_call(select_fns, left[0], right[0])
#     left_rest = left[1:]
#     right_rest = right[1:]
#     recursed = selection_body(left_rest, right_rest)
#     general_answer = recursed.prepend(cur)
#     return ite(vec_size < 1, ListObject.empty(IntObject), general_answer)

# def nested_selection_body(
#     left: ListObject[ListObject[IntObject]],
#     right: ListObject[ListObject[IntObject]],
#     select_op: Choose
# ) -> ListObject[ListObject[IntObject]]:
#     vec_size = left.len()
#     cur = call_elemwise_min(left[0], right[0])
#     recursed = call_nested_elemwise_min(left[1:], right[1:])
#     general_answer = recursed.prepend(cur)
#     return ite(vec_size < 1, ListObject.empty(ListObject[IntObject]), general_answer)
