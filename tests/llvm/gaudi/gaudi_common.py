import typing
from typing import Any, Callable, List, Union

from metalift.frontend.llvm import InvGrammar
from metalift.ir import Bool, Fn, FnDecl, FnDeclRecursive, Int, is_matrix_type
from metalift.ir import List as mlList
from metalift.ir import (Matrix, Object, Synth, call, call_value, choose,
                         fn_decl, fn_decl_recursive, get_list_element_type,
                         get_object_exprs, is_list_type,
                         is_primitive_type, ite)
from metalift.vc_util import and_objects, or_objects

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
SELECTION_TWO_ARGS = "selection_two_args"
NESTED_SELECTION_TWO_ARGS = "nested_selection_two_args"

# Uninterpreted functions
EXP_FN_NAME = "exp"
UNINTERP_DIV_FN_NAME = "uninterp_div"

# Operations that involve uninterpreted functions
VEC_MAP_EXP_FN_NAME = "map_exp"
NESTED_LIST_MAP_EXP_FN_NAME = "nested_list_map_exp"

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
    return call(EXP_FN_NAME, Int, x)

def call_vec_map_exp(x: mlList[Int]) -> mlList[Int]:
    return call(VEC_MAP_EXP_FN_NAME, mlList[Int], x)

def call_nested_list_map_exp(x: Matrix[Int]) -> Matrix[Int]:
    return call(NESTED_LIST_MAP_EXP_FN_NAME, Matrix[Int], x)

def call_uninterp_div(x: Int, y: Int) -> Int:
    return call(UNINTERP_DIV_FN_NAME, Int, x, y)

an_arr2_to_arr = lambda left, right: choose(
    call_vec_elemwise_mul(left, right),
    call_vec_elemwise_add(left, right),
)
an_int_and_arr_to_arr = lambda num, arr: choose(
    call_vec_scalar_mul(num, arr),
    call_vec_scalar_add(num, arr),
    call_vec_scalar_div(num, arr)
)
an_arr_to_int = lambda arr: choose(
    call_reduce_sum(arr),
    call_reduce_mul(arr),
    call_reduce_max(arr)
)
an_arr_to_arr = lambda arr: choose(
    call_vec_map_exp(arr)
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

# Helper functions for selections
def mul8x8_div255_body(int_x: Int, int_y: Int) -> Int:
    return (int_x * int_y) // 255

def screen8x8_body(int_x: Int, int_y: Int) -> Int:
    return int_x + int_y - mul8x8_div255_body(int_x, int_y)

# Selection criteria
def select_darken_blend_body(int_x: Int, int_y: Int) -> Int:
    return ite(int_x > int_y, int_y, int_x)

def select_multiply_blend_body(int_x: Int, int_y: Int) -> Int:
    return mul8x8_div255_body(int_x, int_y)

def select_linear_burn_body(int_x: Int, int_y: Int) -> Int:
    return int_x + int_y - 255

def select_color_burn_body(int_x: Int, int_y: Int) -> Int:
    return ite(
        int_y == 0,
        Int(255),
        255 - (255 - int_x) // int_y
    )

def select_lighten_blend_body(int_x: Int, int_y: Int) -> Int:
    return ite(int_x < int_y, int_y, int_x)

def select_screen_blend_body(int_x: Int, int_y: Int) -> Int:
    return screen8x8_body(int_x, int_y)

def select_linear_dodge_body(int_x: Int, int_y: Int) -> Int:
    return int_x + int_y

def select_color_dodge_body(int_x: Int, int_y: Int) -> Int:
    return ite(
        int_y == 255,
        Int(255),
        int_x // (255 - int_y)
    )

def select_overlay_blend_body(int_x: Int, int_y: Int) -> Int:
    return ite(
        int_x >= 128,
        screen8x8_body(2 * int_x, int_x) - 255,
        mul8x8_div255_body(2 * int_x, int_x)
    )

select_two_args_fn_obj = Fn((Int, Int, Int), SELECT_TWO_ARGS)
select_two_args_fn_decl = fn_decl(SELECT_TWO_ARGS, Int, None, int_x, int_y)
selection_two_args_fn_decl = fn_decl(SELECTION_TWO_ARGS, mlList[Int], None, x, y, select_two_args_fn_obj)

def get_select_two_args_general_synth(
    args: List[Object],
    constants: List[Int],
    compute_ops: List[str],
    compare_ops: List[str],
    depth: int,
) -> Synth:
    # arg_or_cons = choose(arg_expr, Int(0), Int(255))
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

def get_selection_two_args_synth(
    left: mlList[Int],
    right: mlList[Int],
    select_fn: Fn[typing.Tuple[Int, Int, Int]]
) -> Synth:
    return Synth(
        SELECTION_TWO_ARGS,
        selection_two_args_body(left, right, select_fn).src,
        left.src,
        right.src,
        select_fn.src
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
select_two_args_general_synth = get_select_two_args_general_synth(
    args=[int_x, int_y],
    constants=[Int(0), Int(1), Int(128), Int(255)],
    compute_ops=["+", "-", "*", "//"],
    compare_ops=[">=", ">", "==", "<", "<="],
    depth=2
)
selection_two_args_synth = get_selection_two_args_synth(x, y, select_two_args_fn_obj)

def selection_two_args_ps_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    ret_val = writes[0]
    base, active = reads
    # return ret_val == call_nested_selection_two_args(base, active, select_two_args_fn_obj)
    base_or_active = choose(base, active)
    return ret_val == call_nested_selection_two_args(base_or_active, base_or_active, select_two_args_fn_obj)

def selection_two_args_inv0_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    # outer loop grammar
    out, col, pixel, row, row_vec = writes
    base, active = reads
    # return and_objects(
    #     row >= 0,
    #     row <= base.len(),
    #     out == call_nested_selection_two_args(base[:row], active[:row], select_two_args_fn_obj)
    # )
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

def selection_two_args_inv1_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    # inner loop grammar
    col, pixel, row_vec = writes
    out, row = in_scope
    base, active = reads
    # return and_objects(
    #     row >= 0,
    #     row < base.len(),
    #     col >= 0,
    #     col <= base[0].len(),
    #     row_vec == call_selection_two_args(base[row][:col], active[row][:col], select_two_args_fn_obj),
    #     out == call_nested_selection_two_args(base[:row], active[:row], select_two_args_fn_obj)
    # )
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
    constants: List[Int],
    compute_ops: List[str],
    depth: int
):
    def nested_list_computation_ps_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
        ret_val = writes[0]
        base, active = reads
        return ret_val == nested_list_computation(
            args=[base, active],
            constants=constants,
            compute_ops=compute_ops,
            depth=depth
        )
    return nested_list_computation_ps_grammar_fn

def get_nested_list_computation_inv0_grammar_fn(
    constants: List[Int],
    compute_ops: List[str],
    depth: int
):
    def nested_list_computation_inv0_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
        # outer loop grammar
        out, col, pixel, row, row_vec = writes
        base, active = reads
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
    return nested_list_computation_inv0_grammar_fn

def get_nested_list_computation_inv1_grammar_fn(
    constants: List[Int],
    compute_ops: List[str],
    depth: int
):
    def nested_list_computation_inv1_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
        # inner loop grammar
        col, pixel, row_vec = writes
        out, row = in_scope
        base, active = reads
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
    return nested_list_computation_inv1_grammar_fn

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

def get_nested_list_computation_grammars(
    constants: List[Int],
    compute_ops: List[str],
    depth: int
):
    inv0_grammar = InvGrammar(
        get_nested_list_computation_inv0_grammar_fn(
            constants=constants,
            compute_ops=compute_ops,
            depth=depth
        ),
        []
    )
    inv1_grammar = InvGrammar(
        get_nested_list_computation_inv1_grammar_fn(
            constants=constants,
            compute_ops=compute_ops,
            depth=depth
        ),
        ["row", "agg.result"]
    )
    ps_grammar = get_nested_list_computation_ps_grammar_fn(
        constants=constants,
        compute_ops=compute_ops,
        depth=depth
    )
    return inv0_grammar, inv1_grammar, ps_grammar

# Uninterpreted functions
exp = fn_decl(EXP_FN_NAME, Int, None, int_x)
vec_exp_map = fn_decl_recursive(
    VEC_MAP_EXP_FN_NAME,
    mlList[Int],
    map_body(
        vec_or_nested_list=x,
        map_fn=lambda int_x: call_exp(int_x),
        vec_map_fn_name=VEC_MAP_EXP_FN_NAME,
        nested_list_map_fn_name=NESTED_LIST_MAP_EXP_FN_NAME
    ),
    x
)
nested_list_exp_map = fn_decl_recursive(
    NESTED_LIST_MAP_EXP_FN_NAME,
    mlList[Int],
    map_body(
        vec_or_nested_list=nested_x,
        map_fn=lambda int_x: call_exp(int_x),
        vec_map_fn_name=VEC_MAP_EXP_FN_NAME,
        nested_list_map_fn_name=NESTED_LIST_MAP_EXP_FN_NAME
    ),
    nested_x
)

uninterp_div = fn_decl(UNINTERP_DIV_FN_NAME, Int, None, int_x, int_y)