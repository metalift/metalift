import time
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Matrix, Object, choose, ite
from metalift.vc_util import and_objects
from tenspiler.codegen.utils import DataType
from tenspiler.tenspiler_common import (
    call_matrix_vec_mul,
    call_reduce_sum,
    call_vec_elemwise_mul,
    call_vec_scalar_mul,
    get_no_arg_bool_fn,
    matrix_vec_mul,
    reduce_sum,
    vec_elemwise_mul,
    vec_scalar_mul,
)
from tenspiler.utils.synthesis_utils import run_synthesis_algorithm
from tenspiler.axioms_tenspiler import (
    vec_elemwise_mul_axiom,
    reduce_sum_axiom,
    matrix_vec_mul_axiom,
)

# Some loop functions
matrix_outer_loop_index_first_fn_name = "MATRIX_OUTER_LOOP_INDEX_FIRST"
(
    matrix_outer_loop_index_first_fn_decl,
    matrix_outer_loop_index_first_synth,
    is_matrix_outer_loop_index_first,
) = get_no_arg_bool_fn(matrix_outer_loop_index_first_fn_name)

vector_outer_loop_index_fn_name = "VECTOR_OUTER_LOOP_INDEX"
(
    vector_outer_loop_index_fn_decl,
    vector_outer_loop_index_synth,
    is_vector_outer_loop_index,
) = get_no_arg_bool_fn(vector_outer_loop_index_fn_name)


def mat1x3_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        matrix_vec_mul,
        vec_elemwise_mul,
        vec_scalar_mul,
        reduce_sum,
        matrix_outer_loop_index_first_fn_decl,
        vector_outer_loop_index_fn_decl,
        vec_elemwise_mul_axiom,
        reduce_sum_axiom,
        matrix_vec_mul_axiom,
    ]


def mat1x3_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    y = writes[0]
    N, h, x = reads
    matrix = h[:N].col_slice(0, N)
    matrix = choose(matrix, matrix.transpose())
    vec = x[:N]
    return y == call_matrix_vec_mul(matrix, vec)


def mat1x3_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    N, h, x = reads
    y, f, i, sum = writes
    matrix = ite(
        is_matrix_outer_loop_index_first(),
        h[:i].col_slice(0, N),
        h[:N].col_slice(0, i),
    )
    matrix = choose(matrix, matrix.transpose())
    vec = ite(is_vector_outer_loop_index(), x[:i], x[:N])

    return and_objects(i >= 0, i <= N, y == call_matrix_vec_mul(matrix, vec))


def mat1x3_inv1_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    f, sum = writes
    N, h, x = reads
    y, i = in_scope
    outer_loop_matrix = ite(
        is_matrix_outer_loop_index_first(),
        h[:i].col_slice(0, N),
        h[:N].col_slice(0, i),
    )
    outer_loop_matrix = choose(outer_loop_matrix, outer_loop_matrix.transpose())
    outer_loop_vec = ite(is_vector_outer_loop_index(), x[:i], x[:N])

    inner_loop_A_vec = ite(
        is_matrix_outer_loop_index_first(), h[i][:f], h[:f].col_vec(i)
    )
    inner_loop_vec_to_reduce = ite(
        is_vector_outer_loop_index(),
        call_vec_scalar_mul(x[i], inner_loop_A_vec),
        call_vec_elemwise_mul(inner_loop_A_vec, x[:f]),
    )

    return and_objects(
        i >= 0,
        i < N,
        f >= 0,
        f <= N,
        sum == call_reduce_sum(inner_loop_vec_to_reduce),
        y == call_matrix_vec_mul(outer_loop_matrix, outer_loop_vec),
    )


if __name__ == "__main__":
    driver = Driver()
    mat1x3 = driver.analyze(
        llvm_filepath="tenspiler/c2taco/cpp/for_synthesis/dspstone/mat1x3.ll",
        loops_filepath="tenspiler/c2taco/cpp/for_synthesis/dspstone/mat1x3.loops",
        fn_name="mat1x3",
        target_lang_fn=mat1x3_target_lang,
        inv_grammars={
            "mat1x3_inv0": InvGrammar(mat1x3_inv0_grammar, []),
            "mat1x3_inv1": InvGrammar(mat1x3_inv1_grammar, ["i", "agg.result"]),
        },
        ps_grammar=mat1x3_ps_grammar,
    )

    N = Int("N")
    h = Matrix(Int, "h")
    x = mlList(Int, "x")
    driver.add_var_objects([N, h, x])
    driver.add_precondition(N >= 1)
    driver.add_precondition(h.len() >= N)
    driver.add_precondition(h[0].len() >= N)
    driver.add_precondition(x.len() >= N)

    driver.fns_synths = [
        matrix_outer_loop_index_first_synth,
        vector_outer_loop_index_synth,
    ]

    start_time = time.time()
    mat1x3(N, h, x)
    run_synthesis_algorithm(
        driver=driver,
        data_type=DataType.INT32,
        benchmark_name="mat1x3",
        has_relaxed=False,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
