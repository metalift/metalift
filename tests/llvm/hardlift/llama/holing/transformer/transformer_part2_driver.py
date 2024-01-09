from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, Fn, FnDecl, FnDeclRecursive, Int, Matrix, ite
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tests.llvm.hardlift.hardlift_common import call_matrix_vec_mul, call_reduce_sum, call_vec_elemwise_mul, call_vec_scalar_mul, matrix_vec_mul, reduce_sum, vec_elemwise_mul, matrix_vec_to_vec, vec_scalar_mul
from tests.llvm.hardlift.llama.holing.transformer.utils import call_composed_index_fn, get_outer_loop_lower_bound, get_outer_loop_upper_bound, get_inner_loop_lower_bound, get_inner_loop_upper_bound, is_matrix_outer_loop_index_first, is_vector_outer_loop_index, get_outer_loop_index, is_outer_loop_left_bound_smaller, is_outer_loop_left_bound_smaller, common_fn_decls, get_inner_loop_index, is_inner_loop_left_bound_smaller, common_synths

def transformer_part2_inv0_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    # More constrained grammar
    token_position, head, head_size, key_cache_layer, attention = reads
    xb, curr, i, timestep = writes

    composed_int_var = call_composed_index_fn(token_position, head, head_size)
    outer_loop_lower_bound = get_outer_loop_lower_bound(token_position, head, head_size)
    outer_loop_upper_bound = get_outer_loop_upper_bound(token_position, head, head_size)
    inner_loop_lower_bound = get_inner_loop_lower_bound(token_position, head, head_size)
    inner_loop_upper_bound = get_inner_loop_upper_bound(token_position, head, head_size)

    # Get slice indices
    outer_loop_index = get_outer_loop_index(i, timestep)
    outer_loop_index_slice_start = ite(
        is_outer_loop_left_bound_smaller(),
        outer_loop_lower_bound,
        outer_loop_index + 1
    )
    outer_loop_index_slice_end = ite(
        is_outer_loop_left_bound_smaller(),
        outer_loop_index,
        outer_loop_upper_bound
    )

    matrix = ite(
        is_matrix_outer_loop_index_first(),
        key_cache_layer[outer_loop_index_slice_start:outer_loop_index_slice_end].col_slice(
            composed_int_var + inner_loop_lower_bound,
            composed_int_var + inner_loop_upper_bound
        ),
        key_cache_layer[inner_loop_lower_bound:inner_loop_upper_bound].col_slice(
            composed_int_var + outer_loop_index_slice_start,
            composed_int_var + outer_loop_index_slice_end
        )
    )
    matrix = choose(matrix, matrix.transpose())
    vec = ite(
        is_vector_outer_loop_index(),
        attention[outer_loop_index_slice_start:outer_loop_index_slice_end],
        attention[inner_loop_lower_bound:inner_loop_upper_bound]
    )
    return and_objects(
        outer_loop_index >= outer_loop_lower_bound,
        outer_loop_index <= outer_loop_upper_bound,
        xb == matrix_vec_to_vec(matrix, vec)
    )

def transformer_part2_inv1_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    token_position, head, head_size, key_cache_layer, attention = reads
    curr, timestep = writes
    xb, i = in_scope

    composed_int_var = call_composed_index_fn(token_position, head, head_size)
    outer_loop_lower_bound = get_outer_loop_lower_bound(token_position, head, head_size)
    outer_loop_upper_bound = get_outer_loop_upper_bound(token_position, head, head_size)
    inner_loop_lower_bound = get_inner_loop_lower_bound(token_position, head, head_size)
    inner_loop_upper_bound = get_inner_loop_upper_bound(token_position, head, head_size)

    # Get slice indices
    outer_loop_index = get_outer_loop_index(i, timestep)
    inner_loop_index = get_inner_loop_index(i, timestep)
    outer_loop_index_slice_start = ite(
        is_outer_loop_left_bound_smaller(),
        outer_loop_lower_bound,
        outer_loop_index + 1
    )
    outer_loop_index_slice_end = ite(
        is_outer_loop_left_bound_smaller(),
        outer_loop_index,
        outer_loop_upper_bound,
    )
    inner_loop_index_slice_start = ite(
        is_inner_loop_left_bound_smaller(),
        inner_loop_lower_bound,
        inner_loop_index + 1
    )
    inner_loop_index_slice_end = ite(
        is_inner_loop_left_bound_smaller(),
        inner_loop_index,
        inner_loop_upper_bound,
    )

    outer_loop_matrix = ite(
        is_matrix_outer_loop_index_first(),
        key_cache_layer[outer_loop_index_slice_start:outer_loop_index_slice_end]
        .col_slice(
            composed_int_var + inner_loop_lower_bound,
            composed_int_var + inner_loop_upper_bound
        ),
        key_cache_layer[inner_loop_lower_bound:inner_loop_upper_bound]
        .col_slice(
            composed_int_var + outer_loop_index_slice_start,
            composed_int_var + outer_loop_index_slice_end
        )
    )
    outer_loop_matrix = choose(outer_loop_matrix, outer_loop_matrix.transpose())
    outer_loop_vec = ite(
        is_vector_outer_loop_index(),
        attention[outer_loop_index_slice_start:outer_loop_index_slice_end],
        attention[inner_loop_lower_bound:inner_loop_upper_bound]
    )

    inner_loop_key_cache_layer_vec = ite(
        is_matrix_outer_loop_index_first(),
        key_cache_layer[outer_loop_index][
            composed_int_var + inner_loop_index_slice_start:composed_int_var + inner_loop_index_slice_end
        ],
        key_cache_layer[inner_loop_index_slice_start:inner_loop_index_slice_end].col_vec(composed_int_var + outer_loop_index)
    )
    inner_loop_vec_to_reduce = ite(
        is_vector_outer_loop_index(),
        call_vec_scalar_mul(
            attention[outer_loop_index],
            inner_loop_key_cache_layer_vec
        ),
        call_vec_elemwise_mul(
            inner_loop_key_cache_layer_vec,
            attention[inner_loop_index_slice_start:inner_loop_index_slice_end]
        )
    )
    return and_objects(
        outer_loop_index >= outer_loop_lower_bound,
        outer_loop_index < outer_loop_upper_bound,
        inner_loop_index >= inner_loop_lower_bound,
        inner_loop_index <= inner_loop_upper_bound,
        curr == call_reduce_sum(inner_loop_vec_to_reduce),
        xb == call_matrix_vec_mul(outer_loop_matrix, outer_loop_vec)
    )

def transformer_part2_ps_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    token_position, head, head_size, key_cache_layer, attention = reads
    xb = writes[0]
    composed_int_var = call_composed_index_fn(token_position, head, head_size)
    outer_loop_lower_bound = get_outer_loop_lower_bound(token_position, head, head_size)
    outer_loop_upper_bound = get_outer_loop_upper_bound(token_position, head, head_size)
    inner_loop_lower_bound = get_inner_loop_lower_bound(token_position, head, head_size)
    inner_loop_upper_bound = get_inner_loop_upper_bound(token_position, head, head_size)
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
    return xb == matrix_vec_to_vec(matrix, vec)

def transformer_part2_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        reduce_sum,
        vec_elemwise_mul,
        vec_scalar_mul,
        matrix_vec_mul,
        *common_fn_decls
    ]


if __name__ == "__main__":
    driver = Driver()
    transformer_part2 = driver.analyze(
        llvm_filepath="tests/llvm/hardlift/llama/cpp/transformer_part2.ll",
        loops_filepath="tests/llvm/hardlift/llama/cpp/transformer_part2.loops",
        fn_name="transformer_part2",
        target_lang_fn=transformer_part2_target_lang,
        inv_grammars={
            "transformer_part2_inv0": InvGrammar(transformer_part2_inv0_grammar, []),
            "transformer_part2_inv1": InvGrammar(transformer_part2_inv1_grammar, ["i", "agg.result"])
        },
        ps_grammar=transformer_part2_ps_grammar
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

    driver.fns_synths = common_synths
    transformer_part2(
        token_position_var,
        head_var,
        head_size_var,
        key_cache_layer_var,
        attention_var
    )
    driver.synthesize(listBound=3, noVerify=True)