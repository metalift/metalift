import argparse
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Matrix, Object, choose, ite
from metalift.vc_util import and_objects
from tests.llvm.hardlift.hardlift_common import (
    call_matrix_vec_mul,
    call_reduce_sum,
    call_vec_elemwise_mul,
    call_vec_scalar_mul,
    matrix_vec_mul,
    reduce_sum,
    vec_elemwise_mul,
    vec_scalar_mul,
)
from tests.llvm.hardlift.llama.holing.driver.transformer.utils import (
    call_matrix_composed_index_fn,
    common_fn_decls,
    common_synths,
    is_matrix_outer_loop_index_first,
    is_vector_outer_loop_index,
)


def transformer_part2_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    # More constrained grammar
    token_position, head, head_size, key_cache_layer, attention = reads
    xb, curr, i, timestep = writes

    composed_int_var = call_matrix_composed_index_fn(token_position, head, head_size)

    # Get slice indices
    matrix = ite(
        is_matrix_outer_loop_index_first(),
        key_cache_layer[0:i].col_slice(
            composed_int_var,
            composed_int_var + token_position + 1,
        ),
        key_cache_layer[0 : token_position + 1].col_slice(
            composed_int_var,
            composed_int_var + i,
        ),
    )
    matrix = choose(matrix, matrix.transpose())
    vec = ite(
        is_vector_outer_loop_index(),
        attention[0:i],
        attention[0 : token_position + 1],
    )
    return and_objects(
        i >= 0,
        i <= head_size,
        xb == call_matrix_vec_mul(matrix, vec),
    )


def transformer_part2_inv1_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    token_position, head, head_size, key_cache_layer, attention = reads
    curr, timestep = writes
    xb, i = in_scope

    composed_int_var = call_matrix_composed_index_fn(token_position, head, head_size)

    outer_loop_matrix = ite(
        is_matrix_outer_loop_index_first(),
        key_cache_layer[0:i].col_slice(
            composed_int_var,
            composed_int_var + token_position + 1,
        ),
        key_cache_layer[0 : token_position + 1].col_slice(
            composed_int_var,
            composed_int_var + i,
        ),
    )
    outer_loop_matrix = choose(outer_loop_matrix, outer_loop_matrix.transpose())
    outer_loop_vec = ite(
        is_vector_outer_loop_index(),
        attention[0:i],
        attention[0 : token_position + 1],
    )

    inner_loop_key_cache_layer_vec = ite(
        is_matrix_outer_loop_index_first(),
        key_cache_layer[i][composed_int_var : composed_int_var + timestep],
        key_cache_layer[0:timestep].col_vec(composed_int_var + i),
    )
    inner_loop_vec_to_reduce = ite(
        is_vector_outer_loop_index(),
        call_vec_scalar_mul(attention[i], inner_loop_key_cache_layer_vec),
        call_vec_elemwise_mul(
            inner_loop_key_cache_layer_vec,
            attention[0:timestep],
        ),
    )
    return and_objects(
        i >= 0,
        i < head_size,
        timestep >= 0,
        timestep <= token_position + 1,
        curr == call_reduce_sum(inner_loop_vec_to_reduce),
        xb == call_matrix_vec_mul(outer_loop_matrix, outer_loop_vec),
    )


def transformer_part2_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    token_position, head, head_size, key_cache_layer, attention = reads
    xb = writes[0]
    composed_int_var = call_matrix_composed_index_fn(token_position, head, head_size)
    outer_loop_lower_bound = Int(0).maybe_relaxed(parser_args.relaxed)
    outer_loop_upper_bound = token_position.maybe_relaxed(parser_args.relaxed)
    inner_loop_lower_bound = Int(0).maybe_relaxed(parser_args.relaxed)
    inner_loop_upper_bound = head_size.maybe_relaxed(parser_args.relaxed)
    matrix = ite(
        is_matrix_outer_loop_index_first(),
        key_cache_layer[0:head_size].col_slice(
            composed_int_var,
            composed_int_var + token_position + 1,
        ),
        key_cache_layer[0 : token_position + 1].col_slice(
            composed_int_var,
            composed_int_var + head_size,
        ),
    )
    matrix = choose(matrix, matrix.transpose())
    vec = ite(
        is_vector_outer_loop_index(),
        attention[0:head_size],
        attention[0 : token_position + 1],
    )

    return xb == call_matrix_vec_mul(matrix, vec)


def transformer_part2_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        reduce_sum,
        vec_elemwise_mul,
        vec_scalar_mul,
        matrix_vec_mul,
        *common_fn_decls,
    ]


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--list-bound", type=int, required=True)
    parser.add_argument("--rounds-to-guess", type=int, required=True)
    parser.add_argument("--relaxed", action="store_true")
    parser_args = parser.parse_args()

    driver = Driver()
    transformer_part2 = driver.analyze(
        llvm_filepath="tests/llvm/hardlift/llama/cpp/transformer/transformer_part2.ll",
        loops_filepath="tests/llvm/hardlift/llama/cpp/transformer/transformer_part2.loops",
        fn_name="transformer_part2",
        target_lang_fn=transformer_part2_target_lang,
        inv_grammars={
            "transformer_part2_inv0": InvGrammar(transformer_part2_inv0_grammar, []),
            "transformer_part2_inv1": InvGrammar(
                transformer_part2_inv1_grammar, ["i", "agg.result"]
            ),
        },
        ps_grammar=transformer_part2_ps_grammar,
    )
    token_position_var = Int("token_position")
    head_var = Int("head")
    head_size_var = Int("head_size")
    key_cache_layer_var = Matrix(Int, "key_cache_layer")
    attention_var = mlList(Int, "attention")
    driver.add_var_objects(
        [
            token_position_var,
            head_var,
            head_size_var,
            key_cache_layer_var,
            attention_var,
        ]
    )
    driver.add_precondition(token_position_var > 0)

    driver.add_precondition(key_cache_layer_var.len() > 0)
    driver.add_precondition(key_cache_layer_var[0].len() > 0)
    driver.add_precondition(attention_var.len() > 0)
    driver.add_precondition(key_cache_layer_var.len() > token_position_var)
    driver.add_precondition(
        key_cache_layer_var[0].len() > head_var * head_size_var + head_size_var
    )
    driver.add_precondition(attention_var.len() > token_position_var)

    driver.add_precondition(head_var >= 0)
    driver.add_precondition(head_var <= attention_var.len())
    driver.add_precondition(head_size_var > 0)
    driver.add_precondition(head_size_var <= attention_var.len())

    driver.fns_synths = common_synths
    transformer_part2(
        token_position_var, head_var, head_size_var, key_cache_layer_var, attention_var
    )
    rounds_to_guess_suffix = f"_rounds{parser_args.rounds_to_guess}"
    list_bound_suffix = f"_listbound{parser_args.list_bound}"
    relaxed_suffix = "_relaxed" if parser_args.relaxed else ""

    driver.synthesize(
        filename=f"transformer_part2{rounds_to_guess_suffix}{list_bound_suffix}{relaxed_suffix}",
        listBound=parser_args.list_bound,
        rounds_to_guess=parser_args.rounds_to_guess,
    )
