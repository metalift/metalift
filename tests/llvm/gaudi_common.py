from typing import List, Union

from mypy.nodes import Statement

from metalift.frontend.llvm import Driver
from metalift.ir import And, Bool, BoolLit, Call, Choose, Eq, Expr, FnDecl,FnDeclRecursive, Ge, Gt, Int, IntLit, Ite, Le, ListT, Lt, Var, Add, Mul, Sub, Implies
from tests.python.utils.utils import codegen

VECTORADD = "vector_add"
ELEMWISEMUL = "elemwise_mul"
SCALARMUL = "scalar_mul"
BROADCASTADD = "broadcast_add"
REDUCESUM = "reduce_sum"
REDUCEMUL = "reduce_mul"

def ml_list_get(lst, i):
    return Call("list_get", Int(), lst, i)

def ml_list_head(lst):
    return ml_list_get(lst, IntLit(0))

def ml_list_tail(lst, i):
    return Call("list_tail", ListT(Int()), lst, i)

def ml_list_prepend(e, lst):
    return Call("list_prepend", ListT(Int()), e, lst)

def ml_list_length(lst):
    return Call("list_length", Int(), lst)

def ml_list_empty():
    return Call("list_empty", ListT(Int()))

def ml_list_take(lst, i):
    return Call("list_take", ListT(Int()), lst, i)

def call_vector_add(left, right):
    return Call(VECTORADD, ListT(Int()), left, right)

def call_scalar_mul(left, right):
    return Call(SCALARMUL, ListT(Int()), left, right)

def call_broadcast_add(left, right):
    return Call(BROADCASTADD, ListT(Int()), left, right)

def call_reduce_sum(lst):
    return Call(REDUCESUM, Int(), lst)

def call_reduce_mul(lst):
    return Call(REDUCEMUL, Int(), lst)

def call_elemwise_mul(left, right):
    return Call(ELEMWISEMUL, ListT(Int()), left, right)

an_arr2_to_arr = lambda left, right: Choose(
    call_elemwise_mul(left, right),
    call_vector_add(left, right),
)
an_int_and_arr_to_arr = lambda num, arr: Choose(
    call_scalar_mul(num, arr),
    call_broadcast_add(num, arr),
)
an_arr_to_int = lambda arr: Choose(
    call_reduce_sum(arr),
    call_reduce_mul(arr),
)

def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    x = Var("x", ListT(Int()))
    y = Var("y", ListT(Int()))
    a = Var("a", Int())
    b = Var("b", Int())

    def vector_add_body(left, right):
        vec_size = ml_list_length(left)
        cur = Add(ml_list_head(left), ml_list_head(right))
        left_rest = ml_list_tail(left, IntLit(1))
        right_rest = ml_list_tail(right, IntLit(1))
        recursed = call_vector_add(left_rest, right_rest)
        general_answer = ml_list_prepend(cur, recursed)
        return Ite(Lt(vec_size, IntLit(1)), ml_list_empty(), general_answer)
    vector_add = FnDeclRecursive(VECTORADD, ListT(Int()), vector_add_body(x, y), x, y)

    def scalar_mul_body(scalar, arr):
        vec_size = ml_list_length(arr)
        cur = Mul(scalar, ml_list_head(arr))
        arr_rest = ml_list_tail(arr, IntLit(1))
        recursed = call_scalar_mul(scalar, arr_rest)
        general_answer = ml_list_prepend(cur, recursed)
        return Ite(Lt(vec_size, IntLit(1)), ml_list_empty(), general_answer)
    scalar_mul = FnDeclRecursive(SCALARMUL, ListT(Int()), scalar_mul_body(a, x), a, x)

    def broadcast_add_body(scalar, arr):
        vec_size = ml_list_length(arr)
        cur = Add(scalar, ml_list_head(arr))
        arr_rest = ml_list_tail(arr, IntLit(1))
        recursed = call_broadcast_add(scalar, arr_rest)
        general_answer = ml_list_prepend(cur, recursed)
        return Ite(Lt(vec_size, IntLit(1)), ml_list_empty(), general_answer)
    broadcast_add = FnDeclRecursive(BROADCASTADD, ListT(Int()), broadcast_add_body(a, x), a, x)

    def reduce_sum_body(lst):
        vec_size = ml_list_length(lst)
        cur = ml_list_head(lst)
        lst_rest = ml_list_tail(lst, IntLit(1))
        recursed = call_reduce_sum(lst_rest)
        general_answer = Add(cur, recursed)
        return Ite(Lt(vec_size, IntLit(1)), IntLit(0), general_answer)
    reduce_sum = FnDeclRecursive(REDUCESUM, Int(), reduce_sum_body(x), x)

    def reduce_mul_body(lst):
        vec_size = ml_list_length(lst)
        cur = ml_list_head(lst)
        lst_rest = ml_list_tail(lst, IntLit(1))
        recursed = call_reduce_mul(lst_rest)
        general_answer = Mul(cur, recursed)
        return Ite(Lt(vec_size, IntLit(1)), IntLit(1), general_answer)
    reduce_mul = FnDeclRecursive(REDUCEMUL, Int(), reduce_mul_body(x), x)

    def elemwise_mul_body(left, right):
        vec_size = ml_list_length(left)
        cur = Mul(ml_list_head(left), ml_list_head(right))
        left_rest = ml_list_tail(left, IntLit(1))
        right_rest = ml_list_tail(right, IntLit(1))
        recursed = call_elemwise_mul(left_rest, right_rest)
        general_answer = ml_list_prepend(cur, recursed)
        return Ite(Lt(vec_size, IntLit(1)), ml_list_empty(), general_answer)
    elemwise_mul = FnDeclRecursive(ELEMWISEMUL, ListT(Int()), elemwise_mul_body(x, y), x, y)

    return [vector_add, elemwise_mul, scalar_mul, broadcast_add, reduce_sum, reduce_mul]