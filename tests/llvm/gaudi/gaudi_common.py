from typing import List

from metalift.ir import (IntObject, ListObject, call, choose, fnDeclRecursive,
                         ite)

VECTORADD = "vector_add"
ELEMWISEMUL = "elemwise_mul"
SCALARMUL = "scalar_mul"
BROADCASTADD = "broadcast_add"
REDUCESUM = "reduce_sum"
REDUCEMUL = "reduce_mul"
ELEMWISEMAX = "elemwise_max"
NESTEDELEMWISEMAX = "nested_elemwise_max"


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

def call_elemwise_max(left: ListObject[IntObject], right: ListObject[IntObject]) -> ListObject[IntObject]:
    return call(ELEMWISEMAX, ListObject[IntObject], left, right)

def call_nested_elemwise_max(
    left: ListObject[ListObject[IntObject]],
    right: ListObject[ListObject[IntObject]]
) -> ListObject[ListObject[IntObject]]:
    return call(NESTEDELEMWISEMAX, ListObject[ListObject[IntObject]], left, right)

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

def vector_add_body(left: ListObject[IntObject], right: ListObject[IntObject]) -> ListObject[IntObject]:
    vec_size = left.len()
    cur = left[0] + right[0]
    left_rest = left[1:]
    right_rest = right[1:]
    recursed = call_vector_add(left_rest, right_rest)
    general_answer = recursed.prepend(cur)
    return ite(vec_size < 1, ListObject.empty(IntObject), general_answer)
vector_add = fnDeclRecursive(VECTORADD, ListObject[IntObject], vector_add_body(x, y), x, y)

def scalar_mul_body(scalar: IntObject, arr: ListObject[IntObject]) -> ListObject[IntObject]:
    vec_size = arr.len()
    cur = scalar * arr[0]
    arr_rest = arr[1:]
    recursed = call_scalar_mul(scalar, arr_rest)
    general_answer = recursed.prepend(cur)
    return ite(vec_size < 1, ListObject.empty(IntObject), general_answer)
scalar_mul = fnDeclRecursive(SCALARMUL, ListObject[IntObject], scalar_mul_body(a, x), a, x)

def broadcast_add_body(scalar: IntObject, arr: ListObject[IntObject]) -> ListObject[IntObject]:
    vec_size = arr.len()
    cur = scalar + arr[0]
    arr_rest = arr[1:]
    recursed = call_broadcast_add(scalar, arr_rest)
    general_answer = recursed.prepend(cur)
    return ite(vec_size < 1, ListObject.empty(IntObject), general_answer)
broadcast_add = fnDeclRecursive(BROADCASTADD, ListObject[IntObject], broadcast_add_body(a, x), a, x)

def reduce_sum_body(lst: List[IntObject]) -> IntObject:
    vec_size = lst.len()
    cur = lst[0]
    lst_rest = lst[1:]
    recursed = call_reduce_sum(lst_rest)
    general_answer = cur + recursed
    return ite(vec_size < 1, IntObject(0), general_answer)
reduce_sum = fnDeclRecursive(REDUCESUM, IntObject, reduce_sum_body(x), x)

def reduce_mul_body(lst: ListObject[IntObject]) -> IntObject:
    vec_size = lst.len()
    cur = lst[0]
    lst_rest = lst[1:]
    recursed = call_reduce_mul(lst_rest)
    general_answer = cur * recursed
    return ite(vec_size < 1, IntObject(1), general_answer)
reduce_mul = fnDeclRecursive(REDUCEMUL, IntObject, reduce_mul_body(x), x)

def elemwise_mul_body(left: ListObject[IntObject], right: ListObject[IntObject]) -> ListObject[IntObject]:
    vec_size = left.len()
    cur = left[0] * right[0]
    left_rest = left[1:]
    right_rest = right[1:]
    recursed = call_elemwise_mul(left_rest, right_rest)
    general_answer = recursed.prepend(cur)
    return ite(vec_size < 1, ListObject.empty(IntObject), general_answer)
elemwise_mul = fnDeclRecursive(ELEMWISEMUL, ListObject[IntObject], elemwise_mul_body(x, y), x, y)

def elemwise_max_body(left: ListObject[IntObject], right: ListObject[IntObject]) -> ListObject[IntObject]:
    vec_size = left.len()
    cur = left[0] * right[0]
    left_rest = left[1:]
    right_rest = right[1:]
    recursed = call_elemwise_max(left_rest, right_rest)
    general_answer = recursed.prepend(cur)
    return ite(vec_size < 1, ListObject.empty(IntObject), general_answer)
elemwise_max = fnDeclRecursive(ELEMWISEMAX, ListObject[IntObject], elemwise_max_body(x, y), x, y)

def nested_elemwise_max_body(
    left: ListObject[ListObject[IntObject]],
    right: ListObject[ListObject[IntObject]]
) -> ListObject[ListObject[IntObject]]:
    vec_size = left.len()
    cur = call_elemwise_max(left[0], right[0])
    recursed = call_nested_elemwise_max(left[1:], right[1:])
    general_answer = recursed.prepend(cur)
    return ite(vec_size < 1, ListObject.empty(ListObject[IntObject]), general_answer)
nested_elemwise_max = fnDeclRecursive(
    NESTEDELEMWISEMAX,
    ListObject[ListObject[IntObject]],
    nested_elemwise_max_body(nested_x, nested_y),
    nested_x,
    nested_y
)

