import time
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int, Matrix, Object, choose, ite
from metalift.vc_util import and_objects
from tenspiler.codegen.utils import DataType
from tenspiler.tenspiler_common import (
    call_matrix_scalar_mul,
    call_vec_scalar_mul,
    get_no_arg_bool_fn,
    matrix_scalar_mul,
    vec_scalar_mul,
)
from tenspiler.utils.synthesis_utils import run_synthesis_algorithm
from tenspiler.axioms_tenspiler import vec_scalar_mul_axiom, matrix_scalar_mul_axiom

# Some loop functions
outer_loop_index_first_fn_name = "OUTER_LOOP_INDEX_FIRST"
(
    outer_loop_index_first_fn_decl,
    outer_loop_index_first_synth,
    is_outer_loop_index_first,
) = get_no_arg_bool_fn(outer_loop_index_first_fn_name)


def matmul_sca_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        vec_scalar_mul,
        matrix_scalar_mul,
        outer_loop_index_first_fn_decl,
        vec_scalar_mul_axiom,
        matrix_scalar_mul_axiom,
    ]


def matmul_sca_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    matA, val, m, n = reads
    out, i, j, _, _ = writes
    matrix = choose(matA)
    scalar = choose(val)
    matrix = ite(
        is_outer_loop_index_first(),
        matrix[:i].col_slice(0, n),
        matrix[:n].col_slice(0, i),
    )
    matrix = choose(matrix, matrix.transpose())
    return and_objects(i >= 0, i <= m, out == call_matrix_scalar_mul(scalar, matrix))


def matmul_sca_inv1_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    matA, val, m, n = reads
    out, i = in_scope
    j, _, row_vec = writes
    matrix = choose(matA)
    scalar = choose(val)
    outer_loop_matrix = ite(
        is_outer_loop_index_first(),
        matrix[:i].col_slice(0, n),
        matrix[:n].col_slice(0, i),
    )
    outer_loop_matrix = choose(outer_loop_matrix, outer_loop_matrix.transpose())

    inner_loop_vec = ite(
        is_outer_loop_index_first(),
        matrix[i][:j],
        matrix[:j].col_vec(i),
    )
    return and_objects(
        i >= 0,
        i < m,
        j >= 0,
        j <= n,
        row_vec == call_vec_scalar_mul(scalar, inner_loop_vec),
        out == call_matrix_scalar_mul(scalar, outer_loop_matrix),
    )


def matmul_sca_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    matA, val, m, n = reads
    out = writes[0]
    scalar = choose(val)
    matrix = choose(matA)
    matrix = ite(
        is_outer_loop_index_first(),
        matrix[:m].col_slice(0, n),
        matrix[:n].col_slice(0, m),
    )
    matrix = choose(matrix, matrix.transpose())
    return out == call_matrix_scalar_mul(scalar, matrix)


if __name__ == "__main__":
    driver = Driver()
    matmul_sca = driver.analyze(
        llvm_filepath="tenspiler/c2taco/cpp/for_synthesis/mathfu/matmul_sca.ll",
        loops_filepath="tenspiler/c2taco/cpp/for_synthesis/mathfu/matmul_sca.loops",
        fn_name="matmul_sca",
        target_lang_fn=matmul_sca_target_lang,
        inv_grammars={
            "matmul_sca_inv0": InvGrammar(matmul_sca_inv0_grammar, []),
            "matmul_sca_inv1": InvGrammar(matmul_sca_inv1_grammar, ["i", "agg.result"]),
        },
        ps_grammar=matmul_sca_ps_grammar,
    )

    matA = Matrix(Int, "matA")
    val = Int("val")
    m = Int("m")
    n = Int("n")
    driver.add_var_objects([matA, val, m, n])

    # Add preconditions
    driver.add_precondition(m >= 1)
    driver.add_precondition(n >= 1)
    driver.add_precondition(matA.len() >= m)
    driver.add_precondition(matA[0].len() >= n)

    driver.fns_synths = [outer_loop_index_first_synth]

    start_time = time.time()
    matmul_sca(matA, val, m, n)
    run_synthesis_algorithm(
        driver=driver,
        data_type=DataType.INT32,
        benchmark_name="matmul_sca",
        has_relaxed=False,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
