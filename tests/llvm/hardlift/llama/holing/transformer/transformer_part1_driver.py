from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int, Matrix, ite
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tests.llvm.hardlift.hardlift_common import (
    call_integer_exp,
    call_map_int_to_int,
    call_reduce_sum,
    call_vec_elemwise_mul,
    call_vec_elemwise_mul,
    call_vec_map,
    call_vec_scalar_mul,
    call_vec_scalar_mul,
    get_map_int_to_int_synth,
    matrix_vec_mul,
    reduce_sum,
    vec_elemwise_mul,
    matrix_vec_to_vec,
    vec_elemwise_div,
    map_int_to_int_fn_obj,
    vec_scalar_mul,
    vec_map,
    map_int_to_int,
    vec_scalar_div,
)
from tests.llvm.hardlift.llama.holing.transformer.utils import (
    call_matrix_composed_index_fn,
    common_fn_decls,
    common_synths,
    is_matrix_outer_loop_index_first,
    is_vector_outer_loop_index,
    get_outer_loop_lower_bound,
    get_outer_loop_upper_bound,
    get_inner_loop_lower_bound,
    get_inner_loop_upper_bound,
    get_outer_loop_index,
    is_outer_loop_left_bound_smaller,
    get_inner_loop_index,
    is_inner_loop_left_bound_smaller,
    vec_composed_index_fn_decl,
    vec_composed_index_synth,
    call_vec_composed_index_fn,
)
from typing import List, Union

driver = Driver()
# Define initial target lang
target_lang = [
    vec_scalar_mul,
    vec_scalar_div,
    vec_elemwise_mul,
    vec_elemwise_div,
    map_int_to_int,
    vec_map,
    reduce_sum,
    matrix_vec_mul,
    vec_composed_index_fn_decl,
    *common_fn_decls,
]

# Define initial synths
int_x = Int("int_x")
driver.add_var_object(int_x)
map_int_to_int_synth = get_map_int_to_int_synth([call_integer_exp(int_x)])
fns_synths = [map_int_to_int_synth, vec_composed_index_synth, *common_synths]


def transformer_part1_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return target_lang


def transformer_part1_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    attention = writes[0]
    token_position, head, head_size, key_cache_layer, q = reads
    matrix_composed_int_var = call_matrix_composed_index_fn(
        token_position, head, head_size
    )
    vec_composed_int_var = call_vec_composed_index_fn(token_position, head, head_size)
    outer_loop_lower_bound = get_outer_loop_lower_bound(token_position, head, head_size)
    outer_loop_upper_bound = get_outer_loop_upper_bound(token_position, head, head_size)
    inner_loop_lower_bound = get_inner_loop_lower_bound(token_position, head, head_size)
    inner_loop_upper_bound = get_inner_loop_upper_bound(token_position, head, head_size)
    key_cache_layer_matrix = ite(
        is_matrix_outer_loop_index_first(),
        key_cache_layer[outer_loop_lower_bound:outer_loop_upper_bound].col_slice(
            matrix_composed_int_var + inner_loop_lower_bound,
            matrix_composed_int_var + inner_loop_upper_bound,
        ),
        key_cache_layer[inner_loop_lower_bound:inner_loop_upper_bound].col_slice(
            matrix_composed_int_var + outer_loop_lower_bound,
            matrix_composed_int_var + outer_loop_upper_bound,
        ),
    )
    key_cache_layer_matrix = choose(
        key_cache_layer_matrix, key_cache_layer_matrix.transpose()
    )
    q_vec = ite(
        is_vector_outer_loop_index(),
        q[
            vec_composed_int_var
            + outer_loop_lower_bound : vec_composed_int_var
            + outer_loop_upper_bound
        ],
        q[
            vec_composed_int_var
            + inner_loop_lower_bound : vec_composed_int_var
            + inner_loop_upper_bound
        ],
    )

    computed_vec = matrix_vec_to_vec(key_cache_layer_matrix, q_vec)
    scalar = choose(Int(0), Int(1))
    int_var = choose(token_position, head, head_size)
    vec = choose(q_vec, computed_vec)
    vec = choose(
        call_vec_elemwise_mul(
            vec, call_vec_map(call_vec_scalar_mul(scalar, vec), map_int_to_int_fn_obj)
        ),
        call_vec_scalar_mul(call_map_int_to_int(int_var), vec),
    )
    return attention == vec


def transformer_part1_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    token_position, head, head_size, key_cache_layer, q = reads
    attention, i, score, timestep = writes

    matrix_composed_int_var = call_matrix_composed_index_fn(
        token_position, head, head_size
    )
    vec_composed_int_var = call_vec_composed_index_fn(token_position, head, head_size)
    outer_loop_lower_bound = get_outer_loop_lower_bound(token_position, head, head_size)
    outer_loop_upper_bound = get_outer_loop_upper_bound(token_position, head, head_size)
    inner_loop_lower_bound = get_inner_loop_lower_bound(token_position, head, head_size)
    inner_loop_upper_bound = get_inner_loop_upper_bound(token_position, head, head_size)

    # Get slice indices
    outer_loop_index = get_outer_loop_index(i, timestep)
    outer_loop_index_slice_start = ite(
        is_outer_loop_left_bound_smaller(), outer_loop_lower_bound, outer_loop_index + 1
    )
    outer_loop_index_slice_end = ite(
        is_outer_loop_left_bound_smaller(), outer_loop_index, outer_loop_upper_bound
    )

    key_cache_layer_matrix = ite(
        is_matrix_outer_loop_index_first(),
        key_cache_layer[
            outer_loop_index_slice_start:outer_loop_index_slice_end
        ].col_slice(
            matrix_composed_int_var + inner_loop_lower_bound,
            matrix_composed_int_var + inner_loop_upper_bound,
        ),
        key_cache_layer[inner_loop_lower_bound:inner_loop_upper_bound].col_slice(
            matrix_composed_int_var + outer_loop_index_slice_start,
            matrix_composed_int_var + outer_loop_index_slice_end,
        ),
    )
    key_cache_layer_matrix = choose(
        key_cache_layer_matrix, key_cache_layer_matrix.transpose()
    )
    q_vec = ite(
        is_vector_outer_loop_index(),
        q[
            vec_composed_int_var
            + outer_loop_index_slice_start : vec_composed_int_var
            + outer_loop_index_slice_end
        ],
        q[
            vec_composed_int_var
            + inner_loop_lower_bound : vec_composed_int_var
            + inner_loop_upper_bound
        ],
    )

    computed_vec = matrix_vec_to_vec(key_cache_layer_matrix, q_vec)
    scalar = choose(Int(0), Int(1))
    int_var = choose(token_position, head, head_size)
    vec = choose(q_vec, computed_vec)
    vec = choose(
        call_vec_elemwise_mul(
            vec, call_vec_map(call_vec_scalar_mul(scalar, vec), map_int_to_int_fn_obj)
        ),
        call_vec_scalar_mul(call_map_int_to_int(int_var), vec),
    )

    return and_objects(
        outer_loop_index >= outer_loop_lower_bound,
        outer_loop_index <= outer_loop_upper_bound,
        attention == vec,
    )


def transformer_part1_inv1_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    token_position, head, head_size, key_cache_layer, q = reads
    i, score = writes
    attention, timestep = in_scope

    matrix_composed_int_var = call_matrix_composed_index_fn(
        token_position, head, head_size
    )
    vec_composed_int_var = call_vec_composed_index_fn(token_position, head, head_size)
    outer_loop_lower_bound = get_outer_loop_lower_bound(token_position, head, head_size)
    outer_loop_upper_bound = get_outer_loop_upper_bound(token_position, head, head_size)
    inner_loop_lower_bound = get_inner_loop_lower_bound(token_position, head, head_size)
    inner_loop_upper_bound = get_inner_loop_upper_bound(token_position, head, head_size)

    # Get slice indices
    outer_loop_index = get_outer_loop_index(i, timestep)
    inner_loop_index = get_inner_loop_index(i, timestep)
    outer_loop_index_slice_start = ite(
        is_outer_loop_left_bound_smaller(), outer_loop_lower_bound, outer_loop_index + 1
    )
    outer_loop_index_slice_end = ite(
        is_outer_loop_left_bound_smaller(),
        outer_loop_index,
        outer_loop_upper_bound,
    )
    inner_loop_index_slice_start = ite(
        is_inner_loop_left_bound_smaller(), inner_loop_lower_bound, inner_loop_index + 1
    )
    inner_loop_index_slice_end = ite(
        is_inner_loop_left_bound_smaller(),
        inner_loop_index,
        inner_loop_upper_bound,
    )

    key_cache_layer_outer_loop_matrix = ite(
        is_matrix_outer_loop_index_first(),
        key_cache_layer[
            outer_loop_index_slice_start:outer_loop_index_slice_end
        ].col_slice(
            matrix_composed_int_var + inner_loop_lower_bound,
            matrix_composed_int_var + inner_loop_upper_bound,
        ),
        key_cache_layer[inner_loop_lower_bound:inner_loop_upper_bound].col_slice(
            matrix_composed_int_var + outer_loop_index_slice_start,
            matrix_composed_int_var + outer_loop_index_slice_end,
        ),
    )
    key_cache_layer_outer_loop_matrix = choose(
        key_cache_layer_outer_loop_matrix, key_cache_layer_outer_loop_matrix.transpose()
    )
    q_outer_loop_vec = ite(
        is_vector_outer_loop_index(),
        q[
            vec_composed_int_var
            + outer_loop_index_slice_start : vec_composed_int_var
            + outer_loop_index_slice_end
        ],
        q[
            vec_composed_int_var
            + inner_loop_lower_bound : vec_composed_int_var
            + inner_loop_upper_bound
        ],
    )

    outer_loop_computed_vec = matrix_vec_to_vec(
        key_cache_layer_outer_loop_matrix, q_outer_loop_vec
    )
    scalar = choose(Int(0), Int(1))
    int_var = choose(token_position, head, head_size)
    outer_loop_vec = choose(q_outer_loop_vec, outer_loop_computed_vec)
    outer_loop_vec = choose(
        call_vec_elemwise_mul(
            outer_loop_vec,
            call_vec_map(
                call_vec_scalar_mul(scalar, outer_loop_vec), map_int_to_int_fn_obj
            ),
        ),
        call_vec_scalar_mul(call_map_int_to_int(int_var), outer_loop_vec),
    )

    inner_loop_key_cache_layer_vec = ite(
        is_matrix_outer_loop_index_first(),
        key_cache_layer[outer_loop_index][
            matrix_composed_int_var
            + inner_loop_index_slice_start : matrix_composed_int_var
            + inner_loop_index_slice_end
        ],
        key_cache_layer[
            inner_loop_index_slice_start:inner_loop_index_slice_end
        ].col_vec(matrix_composed_int_var + outer_loop_index),
    )
    inner_loop_vec_to_reduce = ite(
        is_vector_outer_loop_index(),
        call_vec_scalar_mul(
            q[vec_composed_int_var + outer_loop_index], inner_loop_key_cache_layer_vec
        ),
        call_vec_elemwise_mul(
            inner_loop_key_cache_layer_vec,
            q[
                vec_composed_int_var
                + inner_loop_index_slice_start : vec_composed_int_var
                + inner_loop_index_slice_end
            ],
        ),
    )

    return and_objects(
        outer_loop_index >= outer_loop_lower_bound,
        outer_loop_index < outer_loop_upper_bound,
        inner_loop_index >= inner_loop_lower_bound,
        inner_loop_index <= inner_loop_upper_bound,
        score == call_reduce_sum(inner_loop_vec_to_reduce),
        attention == outer_loop_vec,
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
            "transformer_part1_inv1": InvGrammar(
                transformer_part1_inv1_grammar, ["timestep", "agg.result"]
            ),
        },
        ps_grammar=transformer_part1_ps_grammar,
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

    driver.fns_synths = fns_synths

    transformer_part1(
        token_position_var,
        head_var,
        head_size_var,
        key_cache_layer_var,
        q_var,
    )

    driver.synthesize(listBound=3, rounds_to_guess=10)
