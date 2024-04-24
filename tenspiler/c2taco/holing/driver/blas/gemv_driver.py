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


def gemv_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
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


def gemv_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    y = writes[0]
    M, N, A, x = reads
    matrix = choose(
        ite(
            is_matrix_outer_loop_index_first(),
            A[:M].col_slice(0, N),
            A[:N].col_slice(0, M),
        )
    )

    matrix = choose(matrix, matrix.transpose())
    vec = choose(ite(is_vector_outer_loop_index(), x[:M], x[:N]))
    return y == call_matrix_vec_mul(matrix, vec)


def gemv_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    M, N, A, x = reads
    y, i, j, sum = writes
    matrix = choose(
        ite(
            is_matrix_outer_loop_index_first(),
            A[:i].col_slice(0, N),
            A[:N].col_slice(0, i),
        )
    )
    matrix = choose(matrix, matrix.transpose())
    vec = ite(is_vector_outer_loop_index(), x[:i], x[:N])

    return and_objects(i >= 0, i <= M, y == call_matrix_vec_mul(matrix, vec))


def gemv_inv1_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    j, sum = writes
    M, N, A, x = reads
    y, i = in_scope
    outer_loop_matrix = choose(
        ite(
            is_matrix_outer_loop_index_first(),
            A[:i].col_slice(0, N),
            A[:N].col_slice(0, i),
        )
    )

    outer_loop_matrix = choose(outer_loop_matrix, outer_loop_matrix.transpose())
    outer_loop_vec = choose(ite(is_vector_outer_loop_index(), x[:i], x[:N]))

    inner_loop_A_vec = choose(
        ite(is_matrix_outer_loop_index_first(), A[i][:j], A[:j].col_vec(i))
    )

    inner_loop_vec_to_reduce = choose(
        ite(
            is_vector_outer_loop_index(),
            call_vec_scalar_mul(x[i], inner_loop_A_vec),
            call_vec_elemwise_mul(inner_loop_A_vec, x[:j]),
        )
    )

    return and_objects(
        i >= 0,
        i < M,
        j >= 0,
        j <= N,
        sum == call_reduce_sum(inner_loop_vec_to_reduce),
        y == call_matrix_vec_mul(outer_loop_matrix, outer_loop_vec),
    )


if __name__ == "__main__":
    driver = Driver()
    gemv = driver.analyze(
        llvm_filepath="tenspiler/c2taco/cpp/for_synthesis/blas/gemv.ll",
        loops_filepath="tenspiler/c2taco/cpp/for_synthesis/blas/gemv.loops",
        fn_name="gemv",
        target_lang_fn=gemv_target_lang,
        inv_grammars={
            "gemv_inv0": InvGrammar(gemv_inv0_grammar, []),
            "gemv_inv1": InvGrammar(gemv_inv1_grammar, ["i", "agg.result"]),
        },
        ps_grammar=gemv_ps_grammar,
    )

    M = Int("M")
    N = Int("N")
    A = Matrix(Int, "A")
    x = mlList(Int, "x")
    driver.add_var_objects([M, N, A, x])
    driver.add_precondition(M >= 1)
    driver.add_precondition(N >= 1)
    driver.add_precondition(A.len() >= M)
    driver.add_precondition(A[0].len() >= N)
    driver.add_precondition(x.len() >= N)

    driver.fns_synths = [
        matrix_outer_loop_index_first_synth,
        vector_outer_loop_index_synth,
    ]

    start_time = time.time()
    gemv(M, N, A, x)
    run_synthesis_algorithm(
        driver=driver,
        data_type=DataType.INT32,
        benchmark_name="gemv",
        has_relaxed=False,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
