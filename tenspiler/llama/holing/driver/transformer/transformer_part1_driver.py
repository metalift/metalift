import time
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Matrix, Object, call, choose, fn_decl, ite, synth
from metalift.vc_util import and_objects
from tenspiler.axioms import (
    matrix_vec_mul_axiom,
    reduce_sum_axiom,
    vec_elemwise_div_axiom,
    vec_elemwise_mul_axiom,
    vec_scalar_div_axiom,
    vec_scalar_mul_axiom,
)
from tenspiler.codegen.utils import DataType
from tenspiler.llama.holing.driver.transformer.utils import (
    call_matrix_composed_index_fn,
    call_vec_composed_index_fn,
    common_fn_decls,
    common_synths,
    is_matrix_outer_loop_index_first,
    is_vector_outer_loop_index,
    vec_composed_index_fn_decl,
    vec_composed_index_synth,
)
from tenspiler.tenspiler_common import (
    call_integer_sqrt,
    call_matrix_vec_mul,
    call_reduce_sum,
    call_vec_elemwise_mul,
    call_vec_scalar_div,
    call_vec_scalar_mul,
    matrix_vec_mul,
    matrix_vec_to_vec,
    reduce_sum,
    vec_elemwise_div,
    vec_elemwise_mul,
    vec_scalar_div,
    vec_scalar_mul,
)
from tenspiler.utils.synthesis_utils import run_synthesis_algorithm

token_position_var = Int("token_position")
head1_var = Int("head1")
head_size_var = Int("head_size")
sqrt_arg_fn_name = "SQRT_ARG_FN"
sqrt_arg_fn_decl = fn_decl(
    sqrt_arg_fn_name, Int, None, token_position_var, head1_var, head_size_var
)
sqrt_arg_synth = synth(
    sqrt_arg_fn_name,
    Int(1) * head_size_var,
    token_position_var,
    head1_var,
    head_size_var,
)


def call_sqrt_arg(token_position: Int, head: Int, head_size: Int) -> Int:
    return call(sqrt_arg_fn_name, Int, token_position, head, head_size)


driver = Driver()
# Define initial target lang
target_lang = [
    vec_scalar_mul,
    vec_scalar_div,
    vec_elemwise_mul,
    vec_elemwise_div,
    reduce_sum,
    matrix_vec_mul,
    vec_composed_index_fn_decl,
    sqrt_arg_fn_decl,
    *common_fn_decls,
    vec_scalar_mul_axiom,
    vec_scalar_div_axiom,
    vec_elemwise_mul_axiom,
    vec_elemwise_div_axiom,
    reduce_sum_axiom,
    matrix_vec_mul_axiom,
]

# Define initial synths
fns_synths = [vec_composed_index_synth, sqrt_arg_synth, *common_synths]


def transformer_part1_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return target_lang


def transformer_part1_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    attention = writes[0]
    token_position, head, head_size, key_cache_layer, q = reads
    matrix_composed_int_var = call_matrix_composed_index_fn(
        token_position, head, head_size
    )
    vec_composed_int_var = call_vec_composed_index_fn(token_position, head, head_size)
    key_cache_layer_matrix = ite(
        is_matrix_outer_loop_index_first(),
        key_cache_layer[0:token_position].col_slice(
            matrix_composed_int_var,
            matrix_composed_int_var + head_size,
        ),
        key_cache_layer[0:head_size].col_slice(
            matrix_composed_int_var,
            matrix_composed_int_var + token_position,
        ),
    )
    q_vec = ite(
        is_vector_outer_loop_index(),
        q[vec_composed_int_var : vec_composed_int_var + token_position],
        q[vec_composed_int_var : vec_composed_int_var + head_size],
    )

    computed_vec = call_matrix_vec_mul(key_cache_layer_matrix, q_vec)
    vec = choose(q_vec, computed_vec)
    vec = call_vec_scalar_div(
        call_integer_sqrt(call_sqrt_arg(token_position, head, head_size)), vec
    )

    return attention == vec


def transformer_part1_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    token_position, head, head_size, key_cache_layer, q = reads
    attention, i, score, timestep = writes

    matrix_composed_int_var = call_matrix_composed_index_fn(
        token_position, head, head_size
    )
    vec_composed_int_var = call_vec_composed_index_fn(token_position, head, head_size)

    key_cache_layer_matrix = ite(
        is_matrix_outer_loop_index_first(),
        key_cache_layer[0:timestep].col_slice(
            matrix_composed_int_var,
            matrix_composed_int_var + head_size,
        ),
        key_cache_layer[0:head_size].col_slice(
            matrix_composed_int_var,
            matrix_composed_int_var + timestep,
        ),
    )
    q_vec = ite(
        is_vector_outer_loop_index(),
        q[vec_composed_int_var : vec_composed_int_var + timestep],
        q[vec_composed_int_var : vec_composed_int_var + head_size],
    )

    computed_vec = call_matrix_vec_mul(key_cache_layer_matrix, q_vec)
    vec = choose(q_vec, computed_vec)
    vec = call_vec_scalar_div(
        call_integer_sqrt(call_sqrt_arg(token_position, head, head_size)), vec
    )

    return and_objects(
        timestep >= 0,
        timestep <= token_position,
        attention == vec,
    )


def transformer_part1_inv1_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    token_position, head, head_size, key_cache_layer, q = reads
    i, score = writes
    attention, timestep = in_scope

    matrix_composed_int_var = call_matrix_composed_index_fn(
        token_position, head, head_size
    )
    vec_composed_int_var = call_vec_composed_index_fn(token_position, head, head_size)

    key_cache_layer_outer_loop_matrix = ite(
        is_matrix_outer_loop_index_first(),
        key_cache_layer[0:timestep].col_slice(
            matrix_composed_int_var,
            matrix_composed_int_var + head_size,
        ),
        key_cache_layer[0:head_size].col_slice(
            matrix_composed_int_var,
            matrix_composed_int_var + timestep,
        ),
    )
    q_outer_loop_vec = ite(
        is_vector_outer_loop_index(),
        q[vec_composed_int_var : vec_composed_int_var + timestep],
        q[vec_composed_int_var : vec_composed_int_var + head_size],
    )

    outer_loop_computed_vec = matrix_vec_to_vec(
        key_cache_layer_outer_loop_matrix, q_outer_loop_vec
    )
    outer_loop_vec = choose(q_outer_loop_vec, outer_loop_computed_vec)
    outer_loop_vec = call_vec_scalar_div(
        call_integer_sqrt(call_sqrt_arg(token_position, head, head_size)),
        outer_loop_vec,
    )

    inner_loop_key_cache_layer_vec = ite(
        is_matrix_outer_loop_index_first(),
        key_cache_layer[timestep][
            matrix_composed_int_var : matrix_composed_int_var + i
        ],
        key_cache_layer[0:i].col_vec(matrix_composed_int_var + timestep),
    )
    inner_loop_vec_to_reduce = ite(
        is_vector_outer_loop_index(),
        call_vec_scalar_mul(
            q[vec_composed_int_var + timestep], inner_loop_key_cache_layer_vec
        ),
        call_vec_elemwise_mul(
            inner_loop_key_cache_layer_vec,
            q[vec_composed_int_var : vec_composed_int_var + i],
        ),
    )

    return and_objects(
        timestep >= 0,
        timestep < token_position,
        i >= 0,
        i <= head_size,
        score == call_reduce_sum(inner_loop_vec_to_reduce),
        attention == outer_loop_vec,
    )


if __name__ == "__main__":
    # Synthesize part 1
    transformer_part1 = driver.analyze(
        llvm_filepath="tenspiler/llama/cpp/for_synthesis/transformer/transformer_part1.ll",
        loops_filepath="tenspiler/llama/cpp/for_synthesis/transformer/transformer_part1.loops",
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
    head1_var = Int("head1")
    head_size_var = Int("head_size")
    key_cache_layer_var = Matrix(Int, "key_cache_layer")
    q_var = mlList(Int, "q")
    driver.add_var_objects(
        [token_position_var, head1_var, head_size_var, key_cache_layer_var, q_var]
    )
    driver.add_precondition(token_position_var > 0)
    driver.add_precondition(key_cache_layer_var.len() > token_position_var)
    driver.add_precondition(head1_var >= 0)
    driver.add_precondition(head1_var <= q_var.len())
    driver.add_precondition(head1_var <= key_cache_layer_var.len())
    driver.add_precondition(head_size_var > 0)
    driver.add_precondition(head_size_var <= q_var.len())
    driver.add_precondition(head_size_var <= key_cache_layer_var.len())
    driver.add_precondition(
        (head1_var * head_size_var + head_size_var) < key_cache_layer_var[0].len()
    )
    driver.add_precondition((head1_var * head_size_var + head_size_var) < q_var.len())

    driver.fns_synths = fns_synths

    start_time = time.time()
    transformer_part1(
        token_position_var,
        head1_var,
        head_size_var,
        key_cache_layer_var,
        q_var,
    )
    run_synthesis_algorithm(
        driver=driver,
        data_type=DataType.INT32,
        benchmark_name="transformer_part1",
        has_relaxed=False,
        list_bound_start=3,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
