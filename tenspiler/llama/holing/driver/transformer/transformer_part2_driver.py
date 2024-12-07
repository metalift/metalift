import time
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Matrix, Object, choose, ite
from metalift.vc_util import and_objects
from tenspiler.axioms import (
    matrix_vec_mul_axiom,
    reduce_sum_axiom,
    vec_elemwise_mul_axiom,
    vec_scalar_mul_axiom,
)
from tenspiler.codegen.utils import DataType
from tenspiler.llama.holing.driver.transformer.utils import (
    call_matrix_composed_index_fn,
    common_fn_decls,
    common_synths,
    is_matrix_outer_loop_index_first,
    is_vector_outer_loop_index,
)
from tenspiler.tenspiler_common import (
    call_matrix_vec_mul,
    call_reduce_sum,
    call_vec_elemwise_mul,
    call_vec_scalar_mul,
    matrix_vec_mul,
    reduce_sum,
    vec_elemwise_mul,
    vec_scalar_mul,
)
from tenspiler.utils.synthesis_utils import run_synthesis_algorithm


def transformer_part2_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
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
    matrix = choose(matrix.transpose())
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
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
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
    outer_loop_matrix = choose(outer_loop_matrix.transpose())
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
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    token_position, head, head_size, key_cache_layer, attention = reads
    xb = writes[0]
    composed_int_var = call_matrix_composed_index_fn(token_position, head, head_size)
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
    matrix = choose(matrix.transpose())
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
        matrix_vec_mul_axiom,
        reduce_sum_axiom,
        vec_elemwise_mul_axiom,
        vec_scalar_mul_axiom,
    ]


if __name__ == "__main__":
    driver = Driver()
    transformer_part2 = driver.analyze(
        llvm_filepath="tenspiler/llama/cpp/for_synthesis/transformer/transformer_part2.ll",
        loops_filepath="tenspiler/llama/cpp/for_synthesis/transformer/transformer_part2.loops",
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
    head1_var = Int("head1")
    head_size_var = Int("head_size")
    key_cache_layer_var = Matrix(Int, "key_cache_layer")
    attention_var = mlList(Int, "attention")
    driver.add_var_objects(
        [
            token_position_var,
            head1_var,
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
        key_cache_layer_var[0].len() > head1_var * head_size_var + head_size_var
    )
    driver.add_precondition(attention_var.len() > token_position_var)

    driver.add_precondition(head1_var >= 0)
    driver.add_precondition(head1_var <= attention_var.len())
    driver.add_precondition(head_size_var > 0)
    driver.add_precondition(head_size_var <= attention_var.len())

    driver.fns_synths = common_synths

    start_time = time.time()
    transformer_part2(
        token_position_var, head1_var, head_size_var, key_cache_layer_var, attention_var
    )
    run_synthesis_algorithm(
        driver=driver,
        data_type=DataType.INT32,
        benchmark_name="transformer_part2",
        has_relaxed=False,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
