import time
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int, Matrix, Object, choose, ite
from metalift.vc_util import and_objects
from tenspiler.tenspiler_common import (
    call_matrix_elemwise_sub,
    call_vec_elemwise_sub,
    get_no_arg_bool_fn,
    matrix_elemwise_sub,
    vec_elemwise_sub,
)

# Some loop functions
outer_loop_index_first_fn_name = "OUTER_LOOP_INDEX_FIRST"
(
    outer_loop_index_first_fn_decl,
    outer_loop_index_first_synth,
    is_outer_loop_index_first,
) = get_no_arg_bool_fn(outer_loop_index_first_fn_name)


def matsub_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        vec_elemwise_sub,
        matrix_elemwise_sub,
        outer_loop_index_first_fn_decl,
    ]


def matsub_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    matA, matB, m, n = reads
    out, i, j, _, _ = writes
    matrix = choose(matA, matB)
    matrix = ite(
        is_outer_loop_index_first(),
        matrix[:i].col_slice(0, n),
        matrix[:n].col_slice(0, i),
    )
    matrix = choose(matrix, matrix.transpose())
    return and_objects(i >= 0, i <= m, out == call_matrix_elemwise_sub(matrix, matrix))


def matsub_inv1_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    matA, matB, m, n = reads
    out, i = in_scope
    j, _, row_vec = writes
    matrix = choose(matA, matB)
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
        row_vec == call_vec_elemwise_sub(inner_loop_vec, inner_loop_vec),
        out == call_matrix_elemwise_sub(outer_loop_matrix, outer_loop_matrix),
    )


def matsub_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    matA, matB, m, n = reads
    out = writes[0]
    matrix = choose(matA, matB)
    matrix = ite(
        is_outer_loop_index_first(),
        matrix[:m].col_slice(0, n),
        matrix[:n].col_slice(0, m),
    )
    matrix = choose(matrix, matrix.transpose())
    return out == call_matrix_elemwise_sub(matrix, matrix)


if __name__ == "__main__":
    driver = Driver()
    matsub = driver.analyze(
        llvm_filepath="tenspiler/c2taco/cpp/for_synthesis/dsp/matsub.ll",
        loops_filepath="tenspiler/c2taco/cpp/for_synthesis/dsp/matsub.loops",
        fn_name="matsub",
        target_lang_fn=matsub_target_lang,
        inv_grammars={
            "matsub_inv0": InvGrammar(matsub_inv0_grammar, []),
            "matsub_inv1": InvGrammar(matsub_inv1_grammar, ["i", "agg.result"]),
        },
        ps_grammar=matsub_ps_grammar,
    )

    matA = Matrix(Int, "matA")
    matB = Matrix(Int, "matB")
    m = Int("m")
    n = Int("n")
    driver.add_var_objects([matA, matB, m, n])

    # Add preconditions
    driver.add_precondition(m >= 1)
    driver.add_precondition(n >= 1)
    driver.add_precondition(matA.len() >= m)
    driver.add_precondition(matB.len() >= m)
    driver.add_precondition(matA[0].len() >= n)
    driver.add_precondition(matB[0].len() >= n)

    driver.fns_synths = [outer_loop_index_first_synth]
    matsub(matA, matB, m, n)

    start_time = time.time()
    driver.synthesize(filename="matsub", no_verify=True)
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
