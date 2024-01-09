
from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int, Matrix, fn_decl, ite
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tests.llvm.hardlift.hardlift_common import call_integer_exp, call_reduce_sum, call_vec_elemwise_div, call_vec_elemwise_mul, call_vec_map, call_vec_scalar_mul, get_fn_and_rv, get_map_int_to_int_synth, matrix_vec_mul, reduce_sum, vec_elemwise_mul, matrix_vec_to_vec, reduce_mul, reduce_max, vec_elemwise_add, vec_elemwise_sub, vec_elemwise_div, map_int_to_int_fn_obj, vec_scalar_mul, vec_to_vec, vec_to_int, matrix_vec_to_vec_target_lang, vec_map, map_int_to_int
from tests.llvm.hardlift.llama.holing.transformer.utils import call_composed_index_fn, common_fn_decls, common_synths, is_matrix_outer_loop_index_first, is_vector_outer_loop_index, get_outer_loop_lower_bound, get_outer_loop_upper_bound, get_inner_loop_lower_bound, get_inner_loop_upper_bound, get_outer_loop_index, is_outer_loop_left_bound_smaller, get_inner_loop_index, is_inner_loop_left_bound_smaller
from typing import Any, List, Union, Tuple

driver = Driver()
# Define initial target lang
target_lang = [
    vec_scalar_mul,
    vec_elemwise_mul,
    vec_elemwise_div,
    map_int_to_int,
    vec_map,
    reduce_sum,
    matrix_vec_mul,
    *common_fn_decls
]

# Define initial synths
int_x = Int("int_x")
driver.add_var_object(int_x)
map_int_to_int_synth = get_map_int_to_int_synth([call_integer_exp(int_x)])
fns_synths = [map_int_to_int_synth, *common_synths]

def transformer_part1_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return target_lang

def transformer_part1_ps_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    attention = writes[0]
    token_position, head, head_size, key_cache_layer, q = reads
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
        q[composed_int_var+outer_loop_lower_bound:composed_int_var+outer_loop_upper_bound],
        q[composed_int_var+inner_loop_lower_bound:composed_int_var+inner_loop_upper_bound]
    )

    # Define computed vec
    computed_vec_fn_name = "ps_computed_vec"
    computed_vec_fn_args = [*reads, *writes, *in_scope]
    computed_vec_fn_decl, computed_vec_synth, computed_vec = get_fn_and_rv(
        computed_vec_fn_name,
        matrix_vec_to_vec(matrix, vec),
        computed_vec_fn_args
    )
    target_lang.append(computed_vec_fn_decl)
    fns_synths.append(computed_vec_synth)

    vec = choose(vec, computed_vec)

    scalar = choose(Int(0), Int(1))
    rhs_vec = call_vec_map(call_vec_scalar_mul(scalar, vec), map_int_to_int_fn_obj)

    # return attention == computed_vec
    return attention == call_vec_elemwise_div(vec, rhs_vec)

def transformer_part1_inv0_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    token_position, head, head_size, key_cache_layer, q = reads
    attention, i, score, timestep = writes

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
        q[composed_int_var+outer_loop_index_slice_start:composed_int_var+outer_loop_index_slice_end],
        q[composed_int_var+inner_loop_lower_bound:composed_int_var+inner_loop_upper_bound]
    )

    # Define computed vec
    computed_vec_fn_name = "inv0_computed_vec"
    computed_vec_fn_args = [*reads, *writes, *in_scope]
    computed_vec_fn_decl, computed_vec_synth, computed_vec = get_fn_and_rv(
        computed_vec_fn_name,
        matrix_vec_to_vec(matrix, vec),
        computed_vec_fn_args
    )
    target_lang.append(computed_vec_fn_decl)
    fns_synths.append(computed_vec_synth)

    vec = choose(vec, computed_vec)

    scalar = choose(Int(0), Int(1))
    rhs_vec = call_vec_map(call_vec_scalar_mul(scalar, vec), map_int_to_int_fn_obj)

    return and_objects(
        outer_loop_index >= outer_loop_lower_bound,
        outer_loop_index <= outer_loop_upper_bound,
        # attention == computed_vec
        attention == call_vec_elemwise_div(vec, rhs_vec)
    )

def transformer_part1_inv1_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    token_position, head, head_size, key_cache_layer, q = reads
    i, score = writes
    attention, timestep = in_scope

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
        q[composed_int_var+outer_loop_index_slice_start:composed_int_var+outer_loop_index_slice_end],
        q[composed_int_var+inner_loop_lower_bound:composed_int_var+inner_loop_upper_bound]
    )
    # Define computed vec
    outer_loop_computed_vec_fn_name = "inv1_computed_vec"
    outer_loop_computed_vec_fn_args = [*reads, *writes, *in_scope]
    outer_loop_computed_vec_fn_decl, outer_loop_computed_vec_synth, outer_loop_computed_vec = get_fn_and_rv(
        outer_loop_computed_vec_fn_name,
        matrix_vec_to_vec(outer_loop_matrix, outer_loop_vec),
        outer_loop_computed_vec_fn_args
    )
    target_lang.append(outer_loop_computed_vec_fn_decl)
    fns_synths.append(outer_loop_computed_vec_synth)

    outer_loop_vec = choose(outer_loop_vec, outer_loop_computed_vec)

    scalar = choose(Int(0), Int(1))
    rhs_outer_loop_vec = call_vec_map(call_vec_scalar_mul(scalar, outer_loop_vec), map_int_to_int_fn_obj)

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
            q[composed_int_var + outer_loop_index],
            inner_loop_key_cache_layer_vec
        ),
        call_vec_elemwise_mul(
            inner_loop_key_cache_layer_vec,
            q[composed_int_var+inner_loop_index_slice_start:composed_int_var+inner_loop_index_slice_end]
        )
    )

    return and_objects(
        outer_loop_index >= outer_loop_lower_bound,
        outer_loop_index < outer_loop_upper_bound,
        inner_loop_index >= inner_loop_lower_bound,
        inner_loop_index <= inner_loop_upper_bound,
        score == call_reduce_sum(inner_loop_vec_to_reduce),
        attention == call_vec_elemwise_div(
            outer_loop_vec,
            rhs_outer_loop_vec
        )
        # attention == outer_loop_computed_vec
    )


if __name__ == "__main__":
    # Synthesize part 1
    transformer_part1 = driver.analyze(
        llvm_filepath="tests/llvm/hardlift/llama/cpp/transformer/transformer_part1.ll",
        loops_filepath="tests/llvm/hardlift/llama/cpp/transformer/transformer_part1.loops",
        fn_name="transformer_part1",
        target_lang_fn=transformer_part1_target_lang,
        inv_grammars={
            "transformer_part1_inv0": InvGrammar(transformer_part1_inv0_grammar, []),
            "transformer_part1_inv1": InvGrammar(transformer_part1_inv1_grammar, ["timestep", "agg.result"])
        },
        ps_grammar=transformer_part1_ps_grammar
    )

    token_position_var = Int("token_position")
    head_var = Int("head")
    head_size_var = Int("head_size")
    key_cache_layer_var = Matrix(Int, "key_cache_layer")
    q_var = mlList(Int, "q")
    driver.add_var_objects([token_position_var, head_var, head_size_var, key_cache_layer_var, q_var])
    driver.add_precondition(token_position_var > 0)
    driver.add_precondition(key_cache_layer_var.len() > token_position_var)
    driver.add_precondition(head_var >= 0)
    driver.add_precondition(head_var <= q_var.len())
    driver.add_precondition(head_var <= key_cache_layer_var.len())
    driver.add_precondition(head_size_var > 0)
    driver.add_precondition(head_size_var <= q_var.len())
    driver.add_precondition(head_size_var <= key_cache_layer_var.len())
    driver.add_precondition((head_var * head_size_var + head_size_var) < key_cache_layer_var[0].len())
    driver.add_precondition((head_var * head_size_var + head_size_var) < q_var.len())

    driver.fns_synths = fns_synths

    transformer_part1(
        token_position_var,
        head_var,
        head_size_var,
        key_cache_layer_var,
        q_var,
    )

    driver.synthesize(listBound=3, rounds_to_guess=5)
