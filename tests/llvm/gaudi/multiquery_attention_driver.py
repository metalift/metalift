from typing import List, Union, Tuple

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, Fn, FnDecl, FnDeclRecursive, Int, Matrix, call, fn_decl, ite, synth
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects, or_objects
from tests.llvm.gaudi.gaudi_common import call_exp, call_map_int_to_int, call_matrix_vec_mul, call_reduce_sum, call_vec_elemwise_div, call_vec_elemwise_mul, call_vec_map, call_vec_scalar_mul, get_map_int_to_int_synth, matrix_vec_mul, reduce_sum, vec_elemwise_mul, vec_vec_to_vec, matrix_vec_to_vec, reduce_mul, reduce_max, vec_elemwise_add, vec_elemwise_sub, vec_elemwise_div, map_int_to_int_fn_obj, vec_map, map_int_to_int, exp, vec_scalar_mul, vec_to_vec, vec_to_int

# Define some helper functions
def get_lower_and_upper_bounds(is_left_bound_smaller: bool, left_bound: Int, right_bound: Int) -> Tuple[Int, Int]:
    lower_bound = ite(
        is_left_bound_smaller,
        left_bound,
        # (for i = {var}; i > {var}; i--): right_bound + 1
        # (for i = {var}; i >= {var}; i--): right_bound
        choose(right_bound, right_bound + 1)
    )
    upper_bound = ite(
        is_left_bound_smaller,
        # (for i = {var}; i < {var}; i++): right_bound - 1
        # (for i = {var}; i <= {var}; i++): right_bound
        choose(right_bound - 1, right_bound),
        left_bound
    ) + 1 # We add 1 here because the upper bound is exclusive
    return lower_bound, upper_bound

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

def multiquery_attention_part1_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        matrix_vec_mul,
        reduce_sum,
        reduce_mul,
        reduce_max,
        vec_elemwise_add,
        vec_elemwise_sub,
        vec_elemwise_mul,
        vec_elemwise_div,
        vec_scalar_mul,
        vec_map,
        map_int_to_int,
        exp
    ]

def multiquery_attention_part1_ps_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    ret_val = writes[0]
    token_position, head, head_size, key_cache_layer, q = reads
    return ret_val == call_matrix_vec_mul(
        key_cache_layer[:token_position].col_slice_with_length(head * head_size, head_size),
        q.slice_with_length(head * head_size, head_size)
    )
    non_zero_int_var = choose(token_position, head, head_size)
    int_var = choose(non_zero_int_var, Int(0))
    slice_index = choose(
        int_var,
        non_zero_int_var * non_zero_int_var + int_var
    )
    matrix = choose(key_cache_layer, key_cache_layer.transpose())
    matrix = choose(
        matrix,
        matrix[slice_index:slice_index],
        matrix[slice_index:slice_index].col_slice(slice_index, slice_index)
    )
    vec = choose(
        q,
        q[slice_index:slice_index],
        matrix[slice_index] # TODO(jie): do we want to include this?
    )
    return ret_val == call_matrix_vec_mul(matrix, vec)

def multiquery_attention_part1_inv0_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    token_position, head, head_size, key_cache_layer, q = reads
    attention, i, score, timestep = writes
    return and_objects(
        timestep >= 0,
        timestep <= token_position,
        attention == call_matrix_vec_mul(
            key_cache_layer[:timestep].col_slice_with_length(head * head_size, head_size),
            q.slice_with_length(head * head_size, head_size)
        )
    )
    non_zero_int_var = choose(
        token_position,
        head,
        head_size,
        i,
        timestep
    )
    int_var = choose(non_zero_int_var, Int(0))
    slice_index = choose(
        int_var,
        non_zero_int_var * non_zero_int_var + int_var
    )

    vec_input = choose(q, q[slice_index:slice_index])
    matrix_input = choose(
        key_cache_layer[:timestep].col_slice(slice_index, slice_index),
        key_cache_layer[:timestep]
    )
    vec = matrix_vec_to_vec(matrix_input, vec_input)
    rhs_vec = call_vec_map(call_vec_scalar_mul(Int(1), vec), map_int_to_int_fn_obj)
    index_lower_bound = choose(Int(0), Int(1))
    index_upper_bound = choose(token_position, head, head_size)
    return and_objects(
        timestep >= index_lower_bound,
        timestep <= index_upper_bound,
        attention == vec
    )

def multiquery_attention_part1_inv1_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    token_position, head, head_size, key_cache_layer, q = reads
    i, score = writes
    attention, timestep = in_scope
    return and_objects(
        timestep >= 0,
        timestep < token_position,
        i >= 0,
        i <= head_size,
        score == call_reduce_sum(
            call_vec_elemwise_mul(
                key_cache_layer[timestep].slice_with_length(head * head_size, i),
                q.slice_with_length(head * head_size, i)
            )
        ),
        attention == call_matrix_vec_mul(
            key_cache_layer[:timestep].col_slice_with_length(head * head_size, head_size),
            q.slice_with_length(head * head_size, head_size)
        )
    )
    non_zero_int_var = choose(token_position, head, head_size, timestep, i)
    int_var = choose(non_zero_int_var, Int(0))
    slice_index = non_zero_int_var * non_zero_int_var + int_var
    vec_input = choose(
        q[slice_index:slice_index],
        q[slice_index:slice_index],
        key_cache_layer[timestep][slice_index:slice_index]
    )
    matrix_input = key_cache_layer[:timestep].col_slice(slice_index, slice_index)
    expected_score = vec_to_int(call_vec_elemwise_mul(vec_input, vec_input))
    vec = matrix_vec_to_vec(matrix_input, vec_input)
    vec_rhs = call_vec_map(
        call_vec_scalar_mul(Int(1), vec),
        map_int_to_int_fn_obj
    )
    lower_bound = choose(Int(0), Int(1))
    upper_bound = choose(token_position, head, head_size)
    return and_objects(
        timestep >= lower_bound,
        timestep < upper_bound,
        i >= lower_bound,
        i <= upper_bound,
        score == expected_score,
        attention == vec
    )

def multiquery_attention_part2_inv0_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    # ## More general grammar
    # token_position, head, head_size, key_cache_layer, attention = reads
    # xb, curr, i, timestep = writes
    # non_zero_int_var = choose(
    #     token_position,
    #     head,
    #     head_size,
    #     i,
    #     timestep
    # )
    # int_var = choose(non_zero_int_var, Int(0))
    # slice_index = choose(int_var, non_zero_int_var * non_zero_int_var + int_var)
    # matrix = choose(key_cache_layer, key_cache_layer.transpose())
    # matrix = choose(
    #     matrix,
    #     matrix[slice_index:slice_index],
    #     matrix[slice_index:slice_index].col_slice(slice_index, slice_index)
    # )
    # vec = choose(
    #     attention,
    #     attention[slice_index:slice_index],
    #     # matrix[slice_index],
    # )
    # general_grammar = and_objects(
    #     i >= 0,
    #     i <= head_size,
    #     xb == call_matrix_vec_mul(matrix, vec)
    # )
    # return general_grammar

    # More constrained grammar
    token_position, head, head_size, key_cache_layer, attention = reads
    xb, curr, i, timestep = writes
    composed_int_var = call_composed_index_fn(token_position, head, head_size)
    outer_loop_lower_bound = get_outer_loop_left_bound(token_position, head, head_size)
    outer_loop_upper_bound = get_outer_loop_right_bound(token_position, head, head_size)
    inner_loop_lower_bound = get_inner_loop_left_bound(token_position, head, head_size)
    inner_loop_upper_bound = get_inner_loop_right_bound(token_position, head, head_size)
    matrix = ite(
        is_matrix_outer_loop_index_first(),
        key_cache_layer[outer_loop_lower_bound:i].col_slice(
            composed_int_var + inner_loop_lower_bound,
            composed_int_var + inner_loop_upper_bound
        ),
        key_cache_layer[inner_loop_lower_bound:inner_loop_upper_bound].col_slice(
            composed_int_var + outer_loop_lower_bound,
            composed_int_var + i
        )
        # key_cache_layer.slice_with_length(0, i).col_slice_with_length(
        #     composed_int_var,
        #     token_position
        # ),
        # key_cache_layer.slice_with_length(0, token_position).col_slice_with_length(
        #     composed_int_var,
        #     i
        # ).transpose(),
    )
    matrix = choose(matrix, matrix.transpose())
    vec = ite(
        is_vector_outer_loop_index(),
        attention[outer_loop_lower_bound:i],
        attention[inner_loop_lower_bound:inner_loop_upper_bound]
    )
    # TODO(jie): we know loop bound is head_size, so vec/matrix cannot be the full thing
    general_grammar = and_objects(
        i >= outer_loop_lower_bound,
        i <= outer_loop_upper_bound,
        xb == call_matrix_vec_mul(matrix, vec)
        # xb == call_matrix_vec_mul(
        #     key_cache_layer[int_index:non_zero_int_index]
        #     .col_slice(
        #         ,
        #         composed_int_index_base + non_zero_int_index
        #     ).transpose(),
        #     attention[int_index:non_zero_int_index]
        # )
        # xb == call_matrix_vec_mul(
        #     key_cache_layer[:token_position]
        #     .col_slice_with_length(
        #         head * head_size,
        #         i
        #     ).transpose(),
        #     attention[:token_position]
        # )
    )
    return general_grammar

def multiquery_attention_part2_inv1_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    token_position, head, head_size, key_cache_layer, attention = reads
    curr, timestep = writes
    xb, i = in_scope
    # return and_objects(
    #     i >= 0,
    #     i < head_size,
    #     timestep >= 0,
    #     timestep <= token_position,
    #     curr == call_reduce_sum(
    #         call_vec_elemwise_mul(
    #             key_cache_layer[:timestep].col_vec(head * head_size + i),
    #             attention_var[:timestep]
    #         )
    #     ),
    #     xb == call_matrix_vec_mul(
    #         key_cache_layer[:token_position]
    #         .col_slice_with_length(
    #             head * head_size,
    #             head * head_size + i
    #         ).transpose(),
    #         attention[:token_position]
    #     )
    # )
    composed_int_var = call_composed_index_fn(token_position, head, head_size)
    outer_loop_lower_bound = get_outer_loop_left_bound(token_position, head, head_size)
    outer_loop_upper_bound = get_outer_loop_right_bound(token_position, head, head_size)
    inner_loop_lower_bound = get_inner_loop_left_bound(token_position, head, head_size)
    inner_loop_upper_bound = get_inner_loop_right_bound(token_position, head, head_size)
    outer_loop_matrix = ite(
        is_matrix_outer_loop_index_first(),
        key_cache_layer[outer_loop_lower_bound:i]
        .col_slice(
            composed_int_var + inner_loop_lower_bound,
            composed_int_var + inner_loop_upper_bound
        ),
        key_cache_layer[inner_loop_lower_bound:inner_loop_upper_bound]
        .col_slice(
            composed_int_var + outer_loop_lower_bound,
            composed_int_var + i
        )
        # key_cache_layer.slice_with_length(0, i).col_slice_with_length(
        #     composed_int_var,
        #     token_position
        # ),
        # key_cache_layer.slice_with_length(0, token_position).col_slice_with_length(
        #     composed_int_var,
        #     i
        # ).transpose()
    )
    outer_loop_matrix = choose(outer_loop_matrix, outer_loop_matrix.transpose())
    outer_loop_vec = ite(
        is_vector_outer_loop_index(),
        attention[outer_loop_lower_bound:i],
        attention[inner_loop_lower_bound:inner_loop_upper_bound]
    )

    inner_loop_key_cache_layer_vec = ite(
        is_matrix_outer_loop_index_first(),
        key_cache_layer[i][composed_int_var + inner_loop_lower_bound:composed_int_var + timestep],
        key_cache_layer[inner_loop_lower_bound:timestep].col_vec(composed_int_var + i)
    )
    inner_loop_vec_to_reduce = ite(
        is_vector_outer_loop_index(),
        call_vec_scalar_mul(
            attention[i],
            inner_loop_key_cache_layer_vec
        ),
        call_vec_elemwise_mul(
            inner_loop_key_cache_layer_vec,
            attention[inner_loop_lower_bound:timestep]
        )
    )
    return and_objects(
        i >= outer_loop_lower_bound,
        i < outer_loop_upper_bound,
        timestep >= inner_loop_lower_bound,
        timestep <= inner_loop_upper_bound,
        curr == call_reduce_sum(inner_loop_vec_to_reduce),
        xb == call_matrix_vec_mul(outer_loop_matrix, outer_loop_vec)
    )
    non_zero_int_var = choose(
        token_position,
        head,
        head_size,
        i,
        timestep
    )
    int_var = choose(non_zero_int_var, Int(0))
    composed_int_var = non_zero_int_var * non_zero_int_var + int_var
    matrix = choose(key_cache_layer, key_cache_layer.transpose())
    matrix = choose(
        matrix,
        matrix[int_var:non_zero_int_var],
        matrix[composed_int_var:composed_int_var]
    )
    matrix = choose(
        matrix,
        matrix.col_slice(composed_int_var, composed_int_var)
    )
    vec = choose(
        attention,
        attention[int_var:non_zero_int_var],
        attention[composed_int_var:composed_int_var],
    )
    matrix_vec = choose(
        matrix[int_var],
        matrix[composed_int_var]
    )
    return and_objects(
        i >= 0,
        i < head_size,
        timestep >= 0,
        timestep <= token_position,
        curr == call_reduce_sum(call_vec_elemwise_mul(matrix_vec, vec)),
        xb == call_matrix_vec_mul(matrix, vec)
    )
    # key_cache_layer_matrix_timestep_slice = key_cache_layer[:timestep].col_slice(head * head_size + i, head * head_size + i + 1).transpose()
    # attention_timestep_slice = attention[:timestep]
    # key_cache_matrix = key_cache_layer[:token_position].col_slice(head * head_size, head * head_size + i)
    # key_cache_matrix_transpose = key_cache_matrix.transpose()
    # return and_objects(
    #     i >= 0,
    #     i < head_size,
    #     timestep >= 0,
    #     timestep <= token_position,
    #     curr == call_reduce_sum(
    #         call_vec_elemwise_mul(
    #             key_cache_layer_matrix_timestep_slice.transpose()[0],
    #             attention_timestep_slice
    #         )
    #     ),
    #     xb == call_matrix_vec_mul(key_cache_matrix_transpose, attention[:token_position])
    # )

def multiquery_attention_part2_ps_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    token_position, head, head_size, key_cache_layer, attention = reads
    xb = writes[0]
    composed_int_var = call_composed_index_fn(token_position, head, head_size)
    outer_loop_left_bound = get_outer_loop_left_bound(token_position, head, head_size)
    outer_loop_right_bound = get_outer_loop_right_bound(token_position, head, head_size)
    inner_loop_left_bound = get_inner_loop_left_bound(token_position, head, head_size)
    inner_loop_right_bound = get_inner_loop_right_bound(token_position, head, head_size)

    outer_loop_lower_bound, outer_loop_upper_bound = get_lower_and_upper_bounds(
        is_outer_loop_left_bound_smaller(),
        outer_loop_left_bound,
        outer_loop_right_bound
    )
    inner_loop_lower_bound, inner_loop_upper_bound = get_lower_and_upper_bounds(
        is_inner_loop_left_bound_smaller(),
        inner_loop_left_bound,
        inner_loop_right_bound
    )

    matrix = ite(
        is_matrix_outer_loop_index_first(),
        key_cache_layer[outer_loop_lower_bound:outer_loop_upper_bound]
        .col_slice(
            composed_int_var + inner_loop_lower_bound,
            composed_int_var + inner_loop_upper_bound
        ),
        key_cache_layer[inner_loop_lower_bound:inner_loop_upper_bound]
        .col_slice(
            composed_int_var + outer_loop_lower_bound,
            composed_int_var + outer_loop_upper_bound
        )
    )
    matrix = choose(matrix, matrix.transpose())
    vec = ite(
        is_vector_outer_loop_index(),
        attention[outer_loop_lower_bound:outer_loop_upper_bound],
        attention[inner_loop_lower_bound:inner_loop_upper_bound]
    )
    return xb == call_matrix_vec_mul(matrix, vec)
    non_zero_int_vars = [token_position, head, head_size]
    non_zero_int_var = choose(*non_zero_int_vars)
    int_index = choose(non_zero_int_var, Int(0))
    # composed_int_var = get_composed_int_var(non_zero_int_vars)
    composed_int_var = head * head_size
    matrix = choose(
        key_cache_layer,
        key_cache_layer.slice_with_length(0, non_zero_int_var),
        key_cache_layer.slice_with_length(0, non_zero_int_var).col_slice_with_length(
            composed_int_var,
            non_zero_int_var
        )
    )
    matrix = choose(matrix, matrix.transpose())
    vec = choose(
        attention,
        attention.slice_with_length(0, non_zero_int_var),
    )
    return xb == call_matrix_vec_mul(matrix, vec)
    # non_zero_int_var = choose(
    #     token_position,
    #     head,
    #     head_size,
    # )
    # int_var = choose(non_zero_int_var, Int(0))
    # composed_int_var = non_zero_int_var * non_zero_int_var + int_var
    # matrix = choose(key_cache_layer, key_cache_layer.transpose())
    # matrix = choose(
    #     matrix,
    #     matrix[int_var:non_zero_int_var],
    #     matrix[composed_int_var:composed_int_var]
    # )
    # matrix = choose(
    #     matrix,
    #     matrix.col_slice(composed_int_var, composed_int_var)
    # )
    # vec = choose(
    #     attention,
    #     attention[int_var:non_zero_int_var],
    #     attention[composed_int_var:composed_int_var],
    # )
    # # return xb == call_matrix_vec_mul(matrix, vec)
    # key_cache_matrix = key_cache_layer[:token_position].col_slice(head * head_size, head * head_size + head_size)
    # key_cache_matrix_transpose = key_cache_matrix.transpose()
    # return xb == call_matrix_vec_mul(key_cache_matrix_transpose, attention[:token_position])

token_position_var = Int("token_position")
head_var = Int("head")
head_size_var = Int("head_size")
composed_index_fn_name = "COMPOSED_INDEX_FN"
composed_index_fn_decl = fn_decl(
    composed_index_fn_name,
    Int,
    None,
    token_position_var,
    head_var,
    head_size_var
)
composed_index_fn_synth = synth(
    composed_index_fn_name,
    get_composed_int_var([token_position_var, head_var, head_size_var]),
    token_position_var,
    head_var,
    head_size_var
)
def call_composed_index_fn(token_position: Int, head: Int, head_size: Int) -> Int:
    return call(composed_index_fn_name, Int, token_position, head, head_size)

matrix_outer_loop_index_first_fn_name = "MATRIX_OUTER_LOOP_INDEX_FIRST"
matrix_outer_loop_index_first_fn_decl = fn_decl(
    matrix_outer_loop_index_first_fn_name,
    Bool,
    None
)
matrix_outer_loop_index_first_fn_synth = synth(
    matrix_outer_loop_index_first_fn_name,
    choose(Bool(True), Bool(False))
)
vector_outer_loop_index_fn_name = "VECTOR_OUTER_LOOP_INDEX"
vector_outer_loop_index_fn_decl = fn_decl(
    vector_outer_loop_index_fn_name,
    Bool,
    None
)
vector_outer_loop_index_fn_synth = synth(
    vector_outer_loop_index_fn_name,
    choose(Bool(True), Bool(False))
)

def is_matrix_outer_loop_index_first() -> Bool:
    return call(matrix_outer_loop_index_first_fn_name, Bool)

def is_vector_outer_loop_index() -> Bool:
    return call(vector_outer_loop_index_fn_name, Bool)


outer_loop_left_bound_fn_name = "OUTER_LOOP_LEFT_BOUND"
outer_loop_left_bound_fn_decl = fn_decl(
    outer_loop_left_bound_fn_name,
    Int,
    None,
    token_position_var,
    head_var,
    head_size_var
)
outer_loop_left_bound_fn_synth = synth(
    outer_loop_left_bound_fn_name,
    Int(0),
    # choose(token_position_var, head_size_var, head_var, Int(0)),
    token_position_var,
    head_var,
    head_size_var
)

outer_loop_right_bound_fn_name = "OUTER_LOOP_RIGHT_BOUND"
outer_loop_right_bound_fn_decl = fn_decl(
    outer_loop_right_bound_fn_name,
    Int,
    None,
    token_position_var,
    head_var,
    head_size_var
)
outer_loop_right_bound_fn_synth = synth(
    outer_loop_right_bound_fn_name,
    head_size_var,
    # choose(token_position_var, head_size_var, head_var),
    token_position_var,
    head_var,
    head_size_var
)

inner_loop_left_bound_fn_name = "INNER_LOOP_LEFT_BOUND"
inner_loop_left_bound_fn_decl = fn_decl(
    inner_loop_left_bound_fn_name,
    Int,
    None,
    token_position_var,
    head_var,
    head_size_var
)
inner_loop_left_bound_fn_synth = synth(
    inner_loop_left_bound_fn_name,
    Int(0),
    # choose(token_position_var, head_size_var, head_var, Int(0)),
    token_position_var,
    head_var,
    head_size_var
)

inner_loop_right_bound_fn_name = "INNER_LOOP_RIGHT_BOUND"
inner_loop_right_bound_fn_decl = fn_decl(
    inner_loop_right_bound_fn_name,
    Int,
    None,
    token_position_var,
    head_var,
    head_size_var
)
inner_loop_right_bound_fn_synth = synth(
    inner_loop_right_bound_fn_name,
    token_position_var,
    # choose(token_position_var, head_size_var, head_var),
    token_position_var,
    head_var,
    head_size_var
)

def get_outer_loop_left_bound(token_position: Int, head: Int, head_size: Int) -> Int:
    return call(outer_loop_left_bound_fn_name, Int, token_position, head, head_size)

def get_outer_loop_right_bound(token_position: Int, head: Int, head_size: Int) -> Int:
    return call(outer_loop_right_bound_fn_name, Int, token_position, head, head_size)

def get_inner_loop_left_bound(token_position: Int, head: Int, head_size: Int) -> Int:
    return call(inner_loop_left_bound_fn_name, Int, token_position, head, head_size)

def get_inner_loop_right_bound(token_position: Int, head: Int, head_size: Int) -> Int:
    return call(inner_loop_right_bound_fn_name, Int, token_position, head, head_size)

outer_loop_left_bound_smaller_fn_name = "OUTER_LOOP_LEFT_BOUND_SMALLER"
outer_loop_left_bound_smaller_fn_decl = fn_decl(
    outer_loop_left_bound_smaller_fn_name,
    Bool,
    None
)
outer_loop_left_bound_smaller_fn_synth = synth(
    outer_loop_left_bound_smaller_fn_name,
    Bool(True)
    # choose(Bool(True), Bool(False))
)
inner_loop_left_bound_smaller_fn_name = "INNER_LOOP_LEFT_BOUND_SMALLER"
inner_loop_left_bound_smaller_fn_decl = fn_decl(
    inner_loop_left_bound_smaller_fn_name,
    Bool,
    None
)
inner_loop_left_bound_smaller_fn_synth = synth(
    inner_loop_left_bound_smaller_fn_name,
    Bool(True)
    # choose(Bool(True), Bool(False))
)

def is_outer_loop_left_bound_smaller() -> Bool:
    return call(outer_loop_left_bound_smaller_fn_name, Bool)

def is_inner_loop_left_bound_smaller() -> Bool:
    return call(inner_loop_left_bound_smaller_fn_name, Bool)

def multiquery_attention_part2_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        reduce_sum,
        vec_elemwise_mul,
        vec_scalar_mul,
        matrix_vec_mul,
        composed_index_fn_decl,
        matrix_outer_loop_index_first_fn_decl,
        vector_outer_loop_index_fn_decl,
        outer_loop_left_bound_fn_decl,
        outer_loop_right_bound_fn_decl,
        inner_loop_left_bound_fn_decl,
        inner_loop_right_bound_fn_decl,
        outer_loop_left_bound_smaller_fn_decl,
        inner_loop_left_bound_smaller_fn_decl
    ]


if __name__ == "__main__":
    # # Synthesize part 1
    # driver = Driver()
    # multiquery_attention_part1 = driver.analyze(
    #     llvm_filepath="tests/llvm/gaudi/multiquery_attention_part1.ll",
    #     loops_filepath="tests/llvm/gaudi/multiquery_attention_part1.loops",
    #     fn_name="multiquery_attention_part1",
    #     target_lang_fn=multiquery_attention_part1_target_lang,
    #     inv_grammars={
    #         "multiquery_attention_part1_inv0": InvGrammar(multiquery_attention_part1_inv0_grammar, []),
    #         "multiquery_attention_part1_inv1": InvGrammar(multiquery_attention_part1_inv1_grammar, ["timestep", "agg.result"])
    #     },
    #     ps_grammar=multiquery_attention_part1_ps_grammar
    # )

    # token_position_var = Int("token_position")
    # head_var = Int("head")
    # head_size_var = Int("head_size")
    # key_cache_layer_var = Matrix(Int, "key_cache_layer")
    # q_var = mlList(Int, "q")
    # driver.add_var_objects([token_position_var, head_var, head_size_var, key_cache_layer_var, q_var])
    # driver.add_precondition(token_position_var > 0)
    # driver.add_precondition(key_cache_layer_var.len() > token_position_var)
    # driver.add_precondition(head_var >= 0)
    # driver.add_precondition(head_var <= q_var.len())
    # driver.add_precondition(head_var <= key_cache_layer_var.len())
    # driver.add_precondition(head_size_var > 0)
    # driver.add_precondition(head_size_var <= q_var.len())
    # driver.add_precondition(head_size_var <= key_cache_layer_var.len())
    # driver.add_precondition((head_var * head_size_var + head_size_var) < key_cache_layer_var[0].len())
    # driver.add_precondition((head_var * head_size_var + head_size_var) < q_var.len())

    # multiquery_attention_part1(
    #     token_position_var,
    #     head_var,
    #     head_size_var,
    #     key_cache_layer_var,
    #     q_var,
    #     uninterp_fns=[exp.name()]
    # )
    # int_x = Int("int_x")
    # map_int_to_int_synth = get_map_int_to_int_synth([call_exp(int_x)])
    # driver.fns_synths = [map_int_to_int_synth]
    # driver.synthesize(listBound=2, noVerify=True)

    driver = Driver()
    multiquery_attention_part2 = driver.analyze(
        llvm_filepath="tests/llvm/gaudi/multiquery_attention_part2.ll",
        loops_filepath="tests/llvm/gaudi/multiquery_attention_part2.loops",
        fn_name="multiquery_attention_part2",
        target_lang_fn=multiquery_attention_part2_target_lang,
        inv_grammars={
            "multiquery_attention_part2_inv0": InvGrammar(multiquery_attention_part2_inv0_grammar, []),
            "multiquery_attention_part2_inv1": InvGrammar(multiquery_attention_part2_inv1_grammar, ["i", "agg.result"])
        },
        ps_grammar=multiquery_attention_part2_ps_grammar
    )
    token_position_var = Int("token_position")
    head_var = Int("head")
    head_size_var = Int("head_size")
    key_cache_layer_var = Matrix(Int, "key_cache_layer")
    attention_var = mlList(Int, "attention")
    driver.add_var_objects([
        token_position_var,
        head_var,
        head_size_var,
        key_cache_layer_var,
        attention_var
    ])
    driver.add_precondition(token_position_var > 0)

    # TODO(jie) are these redundant
    driver.add_precondition(key_cache_layer_var.len() > 0)
    driver.add_precondition(key_cache_layer_var[0].len() > 0)
    driver.add_precondition(attention_var.len() > 0)
    driver.add_precondition(key_cache_layer_var.len() > token_position_var)
    driver.add_precondition(key_cache_layer_var[0].len() > head_var * head_size_var + head_size_var)
    driver.add_precondition(attention_var.len() > token_position_var)

    driver.add_precondition(head_var >= 0)
    driver.add_precondition(head_var <= attention_var.len())
    driver.add_precondition(head_size_var > 0)
    driver.add_precondition(head_size_var <= attention_var.len())

    driver.fns_synths = [
        composed_index_fn_synth,
        matrix_outer_loop_index_first_fn_synth,
        vector_outer_loop_index_fn_synth,
        outer_loop_left_bound_fn_synth,
        outer_loop_right_bound_fn_synth,
        inner_loop_left_bound_fn_synth,
        inner_loop_right_bound_fn_synth,
        outer_loop_left_bound_smaller_fn_synth,
        inner_loop_left_bound_smaller_fn_synth
    ]
    multiquery_attention_part2(
        token_position_var,
        head_var,
        head_size_var,
        key_cache_layer_var,
        attention_var
    )
    # # Add some more assertions
    # curr_var = Int("curr")
    # timestep_var = Int("timestep")
    # token_position_var = Int("token_position")
    # agg_result_var = mlList(Int, "agg.result")
    # i_var = Int("i")
    # driver.asserts.append(
    #     call(
    #         "multiquery_attention_part2_inv1",
    #         Bool,
    #         attention_var,
    #         curr_var,
    #         head_var,
    #         head_size_var,
    #         key_cache_layer_var,
    #         timestep_var,
    #         token_position_var,
    #         agg_result_var,
    #         i_var
    #     ) != and_objects(
    #         i_var >= 0,
    #         i_var < head_size_var,
    #         timestep_var >= 0,
    #         timestep_var <= token_position_var,
    #         curr_var == call_reduce_sum(
    #             call_vec_elemwise_mul(
    #                 key_cache_layer_var[:timestep_var].col_vec(head_var * head_size_var + i_var),
    #                 attention_var[:timestep_var]
    #             )
    #         ),
    #         agg_result_var == call_matrix_vec_mul(
    #             key_cache_layer_var[:token_position_var]
    #             .col_slice(
    #                 head_var * head_size_var,
    #                 head_var * head_size_var + i_var
    #             ).transpose(),
    #             attention_var[:token_position_var]
    #         )
    #     )
    # )

    driver.synthesize(listBound=3, noVerify=True)