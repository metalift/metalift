from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Matrix, Object, call, choose, fn_decl, ite, synth
from metalift.vc_util import and_objects
from tenspiler.tenspiler_common import (
    call_matrix_vec_mul,
    call_reduce_sum,
    call_vec_elemwise_mul,
    call_vec_map,
    call_vec_scalar_mul,
    get_loop_bound_fns,
    map_int_to_int_fn_obj,
    matrix_vec_mul,
    matrix_vec_to_vec,
    reduce_sum,
    vec_elemwise_mul,
    vec_scalar_mul,
    vec_to_int,
)


def multiquery_attention_part1_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        vec_scalar_mul,
        vec_elemwise_mul,
        reduce_sum,
        matrix_vec_mul,
        composed_index_fn_decl,
        matrix_outer_loop_index_first_fn_decl,
        vector_outer_loop_index_fn_decl,
        *outer_loop_fn_decls,
        *inner_loop_fn_decls,
    ]


def multiquery_attention_part1_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    attention = writes[0]
    token_position, head, head_size, key_cache_layer, q = reads
    composed_int_var = call_composed_index_fn(token_position, head, head_size)
    outer_loop_lower_bound = get_outer_loop_lower_bound(token_position, head, head_size)
    outer_loop_upper_bound = get_outer_loop_upper_bound(token_position, head, head_size)
    inner_loop_lower_bound = get_inner_loop_lower_bound(token_position, head, head_size)
    inner_loop_upper_bound = get_inner_loop_upper_bound(token_position, head, head_size)
    matrix = ite(
        is_matrix_outer_loop_index_first(),
        key_cache_layer[outer_loop_lower_bound:outer_loop_upper_bound].col_slice(
            composed_int_var + inner_loop_lower_bound,
            composed_int_var + inner_loop_upper_bound,
        ),
        key_cache_layer[inner_loop_lower_bound:inner_loop_upper_bound].col_slice(
            composed_int_var + outer_loop_lower_bound,
            composed_int_var + outer_loop_upper_bound,
        ),
    )
    matrix = choose(matrix, matrix.transpose())
    vec = ite(
        is_vector_outer_loop_index(),
        q[
            composed_int_var
            + outer_loop_lower_bound : composed_int_var
            + outer_loop_upper_bound
        ],
        q[
            composed_int_var
            + inner_loop_lower_bound : composed_int_var
            + inner_loop_upper_bound
        ],
    )
    return attention == matrix_vec_to_vec(matrix, vec)
    # return ret_val == call_matrix_vec_mul(
    #     key_cache_layer[:token_position].col_slice_with_length(head * head_size, head_size),
    #     q.slice_with_length(head * head_size, head_size)
    # )
    non_zero_int_var = choose(token_position, head, head_size)
    int_var = choose(non_zero_int_var, Int(0))
    slice_index = choose(int_var, non_zero_int_var * non_zero_int_var + int_var)
    matrix = choose(key_cache_layer, key_cache_layer.transpose())
    matrix = choose(
        matrix,
        matrix[slice_index:slice_index],
        matrix[slice_index:slice_index].col_slice(slice_index, slice_index),
    )
    vec = choose(
        q,
        q[slice_index:slice_index],
        matrix[slice_index],  # TODO(jie): do we want to include this?
    )
    return ret_val == call_matrix_vec_mul(matrix, vec)


def multiquery_attention_part1_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    token_position, head, head_size, key_cache_layer, q = reads
    attention, i, score, timestep = writes

    composed_int_var = call_composed_index_fn(token_position, head, head_size)
    outer_loop_lower_bound = get_outer_loop_lower_bound(token_position, head, head_size)
    outer_loop_upper_bound = get_outer_loop_upper_bound(token_position, head, head_size)
    inner_loop_lower_bound = get_inner_loop_lower_bound(token_position, head, head_size)
    inner_loop_upper_bound = get_inner_loop_upper_bound(token_position, head, head_size)
    matrix = ite(
        is_matrix_outer_loop_index_first(),
        key_cache_layer[outer_loop_lower_bound:timestep].col_slice(
            composed_int_var + inner_loop_lower_bound,
            composed_int_var + inner_loop_upper_bound,
        ),
        key_cache_layer[inner_loop_lower_bound:inner_loop_upper_bound].col_slice(
            composed_int_var + outer_loop_lower_bound, composed_int_var + timestep
        ),
    )
    matrix = choose(matrix, matrix.transpose())
    vec = ite(
        is_vector_outer_loop_index(),
        q[composed_int_var + outer_loop_lower_bound : composed_int_var + timestep],
        q[
            composed_int_var
            + inner_loop_lower_bound : composed_int_var
            + inner_loop_upper_bound
        ],
    )
    return and_objects(
        timestep >= outer_loop_lower_bound,
        timestep <= outer_loop_upper_bound,
        attention == matrix_vec_to_vec(matrix, vec),
    )
    return and_objects(
        timestep >= 0,
        timestep <= token_position,
        attention
        == call_matrix_vec_mul(
            key_cache_layer[:timestep].col_slice_with_length(
                head * head_size, head_size
            ),
            q.slice_with_length(head * head_size, head_size),
        ),
    )
    non_zero_int_var = choose(token_position, head, head_size, i, timestep)
    int_var = choose(non_zero_int_var, Int(0))
    slice_index = choose(int_var, non_zero_int_var * non_zero_int_var + int_var)

    vec_input = choose(q, q[slice_index:slice_index])
    matrix_input = choose(
        key_cache_layer[:timestep].col_slice(slice_index, slice_index),
        key_cache_layer[:timestep],
    )
    vec = matrix_vec_to_vec(matrix_input, vec_input)
    rhs_vec = call_vec_map(call_vec_scalar_mul(Int(1), vec), map_int_to_int_fn_obj)
    index_lower_bound = choose(Int(0), Int(1))
    index_upper_bound = choose(token_position, head, head_size)
    return and_objects(
        timestep >= index_lower_bound, timestep <= index_upper_bound, attention == vec
    )


def multiquery_attention_part1_inv1_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    token_position, head, head_size, key_cache_layer, q = reads
    i, score = writes
    attention, timestep = in_scope

    composed_int_var = call_composed_index_fn(token_position, head, head_size)
    outer_loop_lower_bound = get_outer_loop_lower_bound(token_position, head, head_size)
    outer_loop_upper_bound = get_outer_loop_upper_bound(token_position, head, head_size)
    inner_loop_lower_bound = get_inner_loop_lower_bound(token_position, head, head_size)
    inner_loop_upper_bound = get_inner_loop_upper_bound(token_position, head, head_size)

    outer_loop_matrix = ite(
        is_matrix_outer_loop_index_first(),
        key_cache_layer[outer_loop_lower_bound:timestep].col_slice(
            composed_int_var + inner_loop_lower_bound,
            composed_int_var + inner_loop_upper_bound,
        ),
        key_cache_layer[inner_loop_lower_bound:inner_loop_upper_bound].col_slice(
            composed_int_var + outer_loop_lower_bound, composed_int_var + timestep
        ),
    )
    outer_loop_matrix = choose(outer_loop_matrix, outer_loop_matrix.transpose())
    outer_loop_vec = ite(
        is_vector_outer_loop_index(),
        q[composed_int_var + outer_loop_lower_bound : composed_int_var + timestep],
        q[
            composed_int_var
            + inner_loop_lower_bound : composed_int_var
            + inner_loop_upper_bound
        ],
    )

    inner_loop_key_cache_layer_vec = ite(
        is_matrix_outer_loop_index_first(),
        key_cache_layer[timestep][
            composed_int_var + inner_loop_lower_bound : composed_int_var + i
        ],
        key_cache_layer[inner_loop_lower_bound:i].col_vec(composed_int_var + timestep),
    )
    inner_loop_vec_to_reduce = ite(
        is_vector_outer_loop_index(),
        call_vec_scalar_mul(
            q[composed_int_var + timestep], inner_loop_key_cache_layer_vec
        ),
        call_vec_elemwise_mul(
            inner_loop_key_cache_layer_vec,
            q[composed_int_var + inner_loop_lower_bound : composed_int_var + i],
        ),
    )
    return and_objects(
        timestep >= outer_loop_lower_bound,
        timestep < outer_loop_upper_bound,
        i >= inner_loop_lower_bound,
        i <= inner_loop_upper_bound,
        score == call_reduce_sum(inner_loop_vec_to_reduce),
        attention == matrix_vec_to_vec(outer_loop_matrix, outer_loop_vec),
    )
    return and_objects(
        timestep >= 0,
        timestep < token_position,
        i >= 0,
        i <= head_size,
        score
        == call_reduce_sum(
            call_vec_elemwise_mul(
                key_cache_layer[timestep].slice_with_length(head * head_size, i),
                q.slice_with_length(head * head_size, i),
            )
        ),
        attention
        == call_matrix_vec_mul(
            key_cache_layer[:timestep].col_slice_with_length(
                head * head_size, head_size
            ),
            q.slice_with_length(head * head_size, head_size),
        ),
    )
    non_zero_int_var = choose(token_position, head, head_size, timestep, i)
    int_var = choose(non_zero_int_var, Int(0))
    slice_index = non_zero_int_var * non_zero_int_var + int_var
    vec_input = choose(
        q[slice_index:slice_index],
        q[slice_index:slice_index],
        key_cache_layer[timestep][slice_index:slice_index],
    )
    matrix_input = key_cache_layer[:timestep].col_slice(slice_index, slice_index)
    expected_score = vec_to_int(call_vec_elemwise_mul(vec_input, vec_input))
    vec = matrix_vec_to_vec(matrix_input, vec_input)
    vec_rhs = call_vec_map(call_vec_scalar_mul(Int(1), vec), map_int_to_int_fn_obj)
    lower_bound = choose(Int(0), Int(1))
    upper_bound = choose(token_position, head, head_size)
    return and_objects(
        timestep >= lower_bound,
        timestep < upper_bound,
        i >= lower_bound,
        i <= upper_bound,
        score == expected_score,
        attention == vec,
    )


def multiquery_attention_part2_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
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
    outer_loop_lower_bound = get_outer_loop_lower_bound(token_position, head, head_size)
    outer_loop_upper_bound = get_outer_loop_upper_bound(token_position, head, head_size)
    inner_loop_lower_bound = get_inner_loop_lower_bound(token_position, head, head_size)
    inner_loop_upper_bound = get_inner_loop_upper_bound(token_position, head, head_size)

    outer_loop_index = get_outer_loop_index(i, timestep)
    # outer_loop_index = i
    outer_loop_index_slice_start = ite(
        is_outer_loop_left_bound_smaller, outer_loop_lower_bound, outer_loop_index + 1
    )
    outer_loop_index_slice_end = ite(
        is_outer_loop_left_bound_smaller, outer_loop_index, outer_loop_upper_bound
    )
    matrix = ite(
        is_matrix_outer_loop_index_first(),
        key_cache_layer[
            outer_loop_index_slice_start:outer_loop_index_slice_end
        ].col_slice(
            composed_int_var + inner_loop_lower_bound,
            composed_int_var + inner_loop_upper_bound,
        ),
        key_cache_layer[inner_loop_lower_bound:inner_loop_upper_bound].col_slice(
            composed_int_var + outer_loop_index_slice_start,
            composed_int_var + outer_loop_index_slice_end,
        ),
    )
    matrix = choose(matrix, matrix.transpose())
    vec = ite(
        is_vector_outer_loop_index(),
        attention[outer_loop_index_slice_start:outer_loop_index_slice_end],
        attention[inner_loop_lower_bound:inner_loop_upper_bound],
    )
    # TODO(jie): we know loop bound is head_size, so vec/matrix cannot be the full thing
    return and_objects(
        outer_loop_index >= outer_loop_lower_bound,
        outer_loop_index <= outer_loop_upper_bound,
        xb == matrix_vec_to_vec(matrix, vec)
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


def multiquery_attention_part2_inv1_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
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
    outer_loop_lower_bound = get_outer_loop_lower_bound(token_position, head, head_size)
    outer_loop_upper_bound = get_outer_loop_upper_bound(token_position, head, head_size)
    inner_loop_lower_bound = get_inner_loop_lower_bound(token_position, head, head_size)
    inner_loop_upper_bound = get_inner_loop_upper_bound(token_position, head, head_size)
    outer_loop_index = get_outer_loop_index(i, timestep)
    inner_loop_index = get_inner_loop_index(i, timestep)
    # outer_loop_index, inner_loop_index = i, timestep
    outer_loop_index_slice_start = ite(
        is_outer_loop_left_bound_smaller, outer_loop_lower_bound, outer_loop_index + 1
    )
    outer_loop_index_slice_end = ite(
        is_outer_loop_left_bound_smaller,
        outer_loop_index,
        outer_loop_upper_bound,
    )
    inner_loop_index_slice_start = ite(
        is_inner_loop_left_bound_smaller, inner_loop_lower_bound, inner_loop_index + 1
    )
    inner_loop_index_slice_end = ite(
        is_inner_loop_left_bound_smaller,
        inner_loop_index,
        inner_loop_upper_bound,
    )

    outer_loop_matrix = ite(
        is_matrix_outer_loop_index_first(),
        key_cache_layer[
            outer_loop_index_slice_start:outer_loop_index_slice_end
        ].col_slice(
            composed_int_var + inner_loop_lower_bound,
            composed_int_var + inner_loop_upper_bound,
        ),
        key_cache_layer[inner_loop_lower_bound:inner_loop_upper_bound].col_slice(
            composed_int_var + outer_loop_index_slice_start,
            composed_int_var + outer_loop_index_slice_end,
        ),
    )
    outer_loop_matrix = choose(outer_loop_matrix, outer_loop_matrix.transpose())
    outer_loop_vec = ite(
        is_vector_outer_loop_index(),
        attention[outer_loop_index_slice_start:outer_loop_index_slice_end],
        attention[inner_loop_lower_bound:inner_loop_upper_bound],
    )

    inner_loop_key_cache_layer_vec = ite(
        is_matrix_outer_loop_index_first(),
        key_cache_layer[outer_loop_index][
            composed_int_var
            + inner_loop_index_slice_start : composed_int_var
            + inner_loop_index_slice_end
        ],
        key_cache_layer[
            inner_loop_index_slice_start:inner_loop_index_slice_end
        ].col_vec(composed_int_var + outer_loop_index),
    )
    inner_loop_vec_to_reduce = ite(
        is_vector_outer_loop_index(),
        call_vec_scalar_mul(
            attention[outer_loop_index], inner_loop_key_cache_layer_vec
        ),
        call_vec_elemwise_mul(
            inner_loop_key_cache_layer_vec,
            attention[inner_loop_index_slice_start:inner_loop_index_slice_end],
        ),
    )
    return and_objects(
        outer_loop_index >= outer_loop_lower_bound,
        outer_loop_index < outer_loop_upper_bound,
        inner_loop_index >= inner_loop_lower_bound,
        inner_loop_index <= inner_loop_upper_bound,
        curr == call_reduce_sum(inner_loop_vec_to_reduce),
        xb == call_matrix_vec_mul(outer_loop_matrix, outer_loop_vec),
    )
    non_zero_int_var = choose(token_position, head, head_size, i, timestep)
    int_var = choose(non_zero_int_var, Int(0))
    composed_int_var = non_zero_int_var * non_zero_int_var + int_var
    matrix = choose(key_cache_layer, key_cache_layer.transpose())
    matrix = choose(
        matrix,
        matrix[int_var:non_zero_int_var],
        matrix[composed_int_var:composed_int_var],
    )
    matrix = choose(matrix, matrix.col_slice(composed_int_var, composed_int_var))
    vec = choose(
        attention,
        attention[int_var:non_zero_int_var],
        attention[composed_int_var:composed_int_var],
    )
    matrix_vec = choose(matrix[int_var], matrix[composed_int_var])
    return and_objects(
        i >= 0,
        i < head_size,
        timestep >= 0,
        timestep <= token_position,
        curr == call_reduce_sum(call_vec_elemwise_mul(matrix_vec, vec)),
        xb == call_matrix_vec_mul(matrix, vec),
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


def multiquery_attention_part2_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    token_position, head, head_size, key_cache_layer, attention = reads
    xb = writes[0]
    composed_int_var = call_composed_index_fn(token_position, head, head_size)
    outer_loop_lower_bound = get_outer_loop_lower_bound(token_position, head, head_size)
    outer_loop_upper_bound = get_outer_loop_upper_bound(token_position, head, head_size)
    inner_loop_lower_bound = get_inner_loop_lower_bound(token_position, head, head_size)
    inner_loop_upper_bound = get_inner_loop_upper_bound(token_position, head, head_size)
    matrix = ite(
        is_matrix_outer_loop_index_first(),
        key_cache_layer[outer_loop_lower_bound:outer_loop_upper_bound].col_slice(
            composed_int_var + inner_loop_lower_bound,
            composed_int_var + inner_loop_upper_bound,
        ),
        key_cache_layer[inner_loop_lower_bound:inner_loop_upper_bound].col_slice(
            composed_int_var + outer_loop_lower_bound,
            composed_int_var + outer_loop_upper_bound,
        ),
    )
    matrix = choose(matrix, matrix.transpose())
    vec = ite(
        is_vector_outer_loop_index(),
        attention[outer_loop_lower_bound:outer_loop_upper_bound],
        attention[inner_loop_lower_bound:inner_loop_upper_bound],
    )
    return xb == matrix_vec_to_vec(matrix, vec)
    non_zero_int_vars = [token_position, head, head_size]
    non_zero_int_var = choose(*non_zero_int_vars)
    int_index = choose(non_zero_int_var, Int(0))
    # composed_int_var = get_composed_int_var(non_zero_int_vars)
    composed_int_var = head * head_size
    matrix = choose(
        key_cache_layer,
        key_cache_layer.slice_with_length(0, non_zero_int_var),
        key_cache_layer.slice_with_length(0, non_zero_int_var).col_slice_with_length(
            composed_int_var, non_zero_int_var
        ),
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


#### Additional functions to synthesize
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


token_position_var = Int("token_position")
head_var = Int("head")
head_size_var = Int("head_size")
i_var = Int("i")
timestep_var = Int("timestep")

composed_index_fn_name = "COMPOSED_INDEX_FN"
composed_index_fn_decl = fn_decl(
    composed_index_fn_name, Int, None, token_position_var, head_var, head_size_var
)
composed_index_synth = synth(
    composed_index_fn_name,
    get_composed_int_var([token_position_var, head_var, head_size_var]),
    token_position_var,
    head_var,
    head_size_var,
)


def call_composed_index_fn(token_position: Int, head: Int, head_size: Int) -> Int:
    return call(composed_index_fn_name, Int, token_position, head, head_size)


matrix_outer_loop_index_first_fn_name = "MATRIX_OUTER_LOOP_INDEX_FIRST"
matrix_outer_loop_index_first_fn_decl = fn_decl(
    matrix_outer_loop_index_first_fn_name, Bool, None
)
matrix_outer_loop_index_first_synth = synth(
    matrix_outer_loop_index_first_fn_name, choose(Bool(True), Bool(False))
)
vector_outer_loop_index_fn_name = "VECTOR_OUTER_LOOP_INDEX"
vector_outer_loop_index_fn_decl = fn_decl(vector_outer_loop_index_fn_name, Bool, None)
vector_outer_loop_index_synth = synth(
    vector_outer_loop_index_fn_name, choose(Bool(True), Bool(False))
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
    is_outer_loop_left_bound_smaller,
) = get_loop_bound_fns(
    loop_bound_fn_args=loop_bound_fn_args,
    loop_index_fn_args=loop_index_fn_args,
    left_bound_choices=[Int(0)],
    right_bound_choices=loop_bound_fn_args,
    prefix="OUTER_LOOP",
)
(
    inner_loop_fn_decls,
    inner_loop_synths,
    get_inner_loop_lower_bound,
    get_inner_loop_upper_bound,
    get_inner_loop_index,
    is_inner_loop_left_bound_smaller,
) = get_loop_bound_fns(
    loop_bound_fn_args=loop_bound_fn_args,
    loop_index_fn_args=loop_index_fn_args,
    left_bound_choices=[Int(0)],
    right_bound_choices=loop_bound_fn_args,
    prefix="INNER_LOOP",
)


def multiquery_attention_part2_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        reduce_sum,
        vec_elemwise_mul,
        vec_scalar_mul,
        matrix_vec_mul,
        composed_index_fn_decl,
        matrix_outer_loop_index_first_fn_decl,
        vector_outer_loop_index_fn_decl,
        *outer_loop_fn_decls,
        *inner_loop_fn_decls,
    ]


if __name__ == "__main__":
    # Synthesize part 1
    driver = Driver()
    multiquery_attention_part1 = driver.analyze(
        llvm_filepath="tests/llvm/gaudi/multiquery_attention_part1.ll",
        loops_filepath="tests/llvm/gaudi/multiquery_attention_part1.loops",
        fn_name="multiquery_attention_part1",
        target_lang_fn=multiquery_attention_part1_target_lang,
        inv_grammars={
            "multiquery_attention_part1_inv0": InvGrammar(
                multiquery_attention_part1_inv0_grammar, []
            ),
            "multiquery_attention_part1_inv1": InvGrammar(
                multiquery_attention_part1_inv1_grammar, ["timestep", "agg.result"]
            ),
        },
        ps_grammar=multiquery_attention_part1_ps_grammar,
    )

    token_position_var = Int("token_position")
    head_var = Int("head")
    head_size_var = Int("head_size")
    key_cache_layer_var = Matrix(Int, "key_cache_layer")
    q_var = mlList(Int, "q")
    driver.add_var_objects(
        [token_position_var, head_var, head_size_var, key_cache_layer_var, q_var]
    )
    driver.add_precondition(token_position_var > 0)
    driver.add_precondition(key_cache_layer_var.len() > token_position_var)
    driver.add_precondition(head_var >= 0)
    driver.add_precondition(head_var <= q_var.len())
    driver.add_precondition(head_var <= key_cache_layer_var.len())
    driver.add_precondition(head_size_var > 0)
    driver.add_precondition(head_size_var <= q_var.len())
    driver.add_precondition(head_size_var <= key_cache_layer_var.len())
    driver.add_precondition(
        (head_var * head_size_var + head_size_var) < key_cache_layer_var[0].len()
    )
    driver.add_precondition((head_var * head_size_var + head_size_var) < q_var.len())

    driver.fns_synths = [
        composed_index_synth,
        matrix_outer_loop_index_first_synth,
        vector_outer_loop_index_synth,
        *outer_loop_synths,
        *inner_loop_synths,
    ]

    multiquery_attention_part1(
        token_position_var,
        head_var,
        head_size_var,
        key_cache_layer_var,
        q_var,
    )
    int_x = Int("int_x")
    # map_int_to_int_synth = get_map_int_to_int_synth([call_integer_exp(int_x)])
    driver.synthesize(listBound=3, noVerify=True)

    # driver = Driver()
    # multiquery_attention_part2 = driver.analyze(
    #     llvm_filepath="tenspiler/llama/cpp/rmsnorm/multiquery_attention_part2.ll",
    #     loops_filepath="tenspiler/llama/cpp/rmsnorm/multiquery_attention_part2.loops",
    #     fn_name="multiquery_attention_part2",
    #     target_lang_fn=multiquery_attention_part2_target_lang,
    #     inv_grammars={
    #         "multiquery_attention_part2_inv0": InvGrammar(multiquery_attention_part2_inv0_grammar, []),
    #         "multiquery_attention_part2_inv1": InvGrammar(multiquery_attention_part2_inv1_grammar, ["i", "agg.result"])
    #     },
    #     ps_grammar=multiquery_attention_part2_ps_grammar
    # )
    # token_position_var = Int("token_position")
    # head_var = Int("head")
    # head_size_var = Int("head_size")
    # key_cache_layer_var = Matrix(Int, "key_cache_layer")
    # attention_var = mlList(Int, "attention")
    # driver.add_var_objects([
    #     token_position_var,
    #     head_var,
    #     head_size_var,
    #     key_cache_layer_var,
    #     attention_var
    # ])
    # driver.add_precondition(token_position_var > 0)

    # # TODO(jie) are these redundant
    # driver.add_precondition(key_cache_layer_var.len() > 0)
    # driver.add_precondition(key_cache_layer_var[0].len() > 0)
    # driver.add_precondition(attention_var.len() > 0)
    # driver.add_precondition(key_cache_layer_var.len() > token_position_var)
    # driver.add_precondition(key_cache_layer_var[0].len() > head_var * head_size_var + head_size_var)
    # driver.add_precondition(attention_var.len() > token_position_var)

    # driver.add_precondition(head_var >= 0)
    # driver.add_precondition(head_var <= attention_var.len())
    # driver.add_precondition(head_size_var > 0)
    # driver.add_precondition(head_size_var <= attention_var.len())

    # driver.fns_synths = [
    #     composed_index_synth,
    #     matrix_outer_loop_index_first_synth,
    #     vector_outer_loop_index_synth,
    #     *outer_loop_synths,
    #     *inner_loop_synths
    # ]
    # multiquery_attention_part2(
    #     token_position_var,
    #     head_var,
    #     head_size_var,
    #     key_cache_layer_var,
    #     attention_var
    # )
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

    # driver.synthesize(listBound=3, noVerify=True)
