from typing import List
from metalift.ir import Bool, Int, call, choose, fn_decl, synth
from tests.llvm.hardlift.hardlift_common import get_loop_fns

# Define arguments to helper functions to synthesize
token_position_var = Int("token_position")
head_var = Int("head")
head_size_var = Int("head_size")
i_var = Int("i")
timestep_var = Int("timestep")

# Define some helper functions for synthesizing int vars
def get_composed_int_var(int_vars: List[Int]) -> Int:
    return choose(*get_composed_combs(int_vars))

def get_composed_combs(int_vars: List[Int]) -> List[Int]:
    mul_exprs: List[Int] = []
    for lhs_index, lhs_var in enumerate(int_vars):
        for rhs_index in range(lhs_index + 1):
            rhs_var = int_vars[rhs_index]
            mul_exprs.append(lhs_var * rhs_var)
    return mul_exprs

composed_index_fn_name = "COMPOSED_INDEX_FN"
composed_index_fn_decl = fn_decl(
    composed_index_fn_name,
    Int,
    None,
    token_position_var,
    head_var,
    head_size_var
)
composed_index_synth = synth(
    composed_index_fn_name,
    get_composed_int_var([token_position_var, head_var, head_size_var]),
    token_position_var,
    head_var,
    head_size_var
)
def call_composed_index_fn(token_position: Int, head: Int, head_size: Int) -> Int:
    return call(composed_index_fn_name, Int, token_position, head, head_size)

# Loop functions
matrix_outer_loop_index_first_fn_name = "MATRIX_OUTER_LOOP_INDEX_FIRST"
matrix_outer_loop_index_first_fn_decl = fn_decl(
    matrix_outer_loop_index_first_fn_name,
    Bool,
    None
)
matrix_outer_loop_index_first_synth = synth(
    matrix_outer_loop_index_first_fn_name,
    choose(Bool(True), Bool(False))
)
vector_outer_loop_index_fn_name = "VECTOR_OUTER_LOOP_INDEX"
vector_outer_loop_index_fn_decl = fn_decl(
    vector_outer_loop_index_fn_name,
    Bool,
    None
)
vector_outer_loop_index_synth = synth(
    vector_outer_loop_index_fn_name,
    choose(Bool(True), Bool(False))
)

def is_matrix_outer_loop_index_first() -> Bool:
    return call(matrix_outer_loop_index_first_fn_name, Bool)

def is_vector_outer_loop_index() -> Bool:
    return call(vector_outer_loop_index_fn_name, Bool)

# Arguments to all loop functions
loop_bound_fn_args = [token_position_var, head_var, head_size_var]
loop_index_fn_args = [i_var, timestep_var]
(
    outer_loop_fn_decls,
    outer_loop_synths,
    get_outer_loop_lower_bound,
    get_outer_loop_upper_bound,
    get_outer_loop_index,
    is_outer_loop_left_bound_smaller
) = get_loop_fns(
    loop_bound_fn_args=loop_bound_fn_args,
    loop_index_fn_args=loop_index_fn_args,
    left_bound_choices=[Int(0)],
    right_bound_choices=loop_bound_fn_args,
    prefix="OUTER_LOOP"
)
(
    inner_loop_fn_decls,
    inner_loop_synths,
    get_inner_loop_lower_bound,
    get_inner_loop_upper_bound,
    get_inner_loop_index,
    is_inner_loop_left_bound_smaller
) = get_loop_fns(
    loop_bound_fn_args=loop_bound_fn_args,
    loop_index_fn_args=loop_index_fn_args,
    left_bound_choices=[Int(0)],
    right_bound_choices=loop_bound_fn_args,
    prefix="INNER_LOOP"
)

common_fn_decls = [
    composed_index_fn_decl,
    matrix_outer_loop_index_first_fn_decl,
    vector_outer_loop_index_fn_decl,
    *outer_loop_fn_decls,
    *inner_loop_fn_decls
]
common_synths = [
    composed_index_synth,
    matrix_outer_loop_index_first_synth,
    vector_outer_loop_index_synth,
    *outer_loop_synths,
    *inner_loop_synths
]