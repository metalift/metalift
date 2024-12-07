import time
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int, Matrix, Object, choose, ite
from metalift.vc_util import and_objects
from tenspiler.axioms import matrix_scalar_mul_axiom, vec_scalar_mul_axiom
from tenspiler.codegen.utils import DataType
from tenspiler.tenspiler_common import (
    call_matrix_scalar_mul,
    call_vec_scalar_mul,
    get_no_arg_bool_fn,
    matrix_scalar_mul,
    vec_scalar_mul,
)
from tenspiler.utils.synthesis_utils import run_synthesis_algorithm

# Some loop functions
outer_loop_index_first_fn_name = "MATRIX_OUTER_LOOP_INDEX_FIRST"
(
    outer_loop_index_first_fn_decl,
    outer_loop_index_first_synth,
    is_outer_loop_index_first,
) = get_no_arg_bool_fn(outer_loop_index_first_fn_name)


def scale_matrix_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        outer_loop_index_first_fn_decl,
        vec_scalar_mul,
        matrix_scalar_mul,
        vec_scalar_mul_axiom,
        matrix_scalar_mul_axiom,
    ]


def scale_matrix_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    m, scale = reads
    out, i, j, _, _ = writes
    matrix = choose(m)
    scalar = choose(scale)
    matrix = ite(
        is_outer_loop_index_first(),
        matrix[:i],
        matrix.col_slice(0, i),
    )
    matrix = choose(matrix, matrix.transpose())
    return and_objects(
        i >= 0, i <= m.len(), out == call_matrix_scalar_mul(scalar, matrix)
    )


def scale_matrix_inv1_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    m, scale = reads
    out, i = in_scope
    j, _, row_vec = writes
    matrix = choose(m)
    scalar = choose(scale)
    outer_loop_matrix = ite(
        is_outer_loop_index_first(),
        matrix[:i],
        matrix.col_slice(0, i),
    )
    outer_loop_matrix = choose(outer_loop_matrix, outer_loop_matrix.transpose())

    inner_loop_vec = ite(
        is_outer_loop_index_first(),
        matrix[i][:j],
        matrix[:j].col_vec(i),
    )
    return and_objects(
        i >= 0,
        i < m.len(),
        j >= 0,
        j <= m[0].len(),
        row_vec == call_vec_scalar_mul(scalar, inner_loop_vec),
        out == call_matrix_scalar_mul(scalar, outer_loop_matrix),
    )


def scale_matrix_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    m, scale = reads
    out = writes[0]
    matrix = choose(m)
    scalar = choose(scale)
    matrix = choose(matrix, matrix.transpose())
    return out == call_matrix_scalar_mul(scalar, matrix)


if __name__ == "__main__":
    driver = Driver()
    scale_matrix = driver.analyze(
        llvm_filepath="tenspiler/c2taco/cpp/for_synthesis/darknet/scale_matrix.ll",
        loops_filepath="tenspiler/c2taco/cpp/for_synthesis/darknet/scale_matrix.loops",
        fn_name="scale_matrix",
        target_lang_fn=scale_matrix_target_lang,
        inv_grammars={
            "scale_matrix_inv0": InvGrammar(scale_matrix_inv0_grammar, []),
            "scale_matrix_inv1": InvGrammar(
                scale_matrix_inv1_grammar, ["i", "agg.result"]
            ),
        },
        ps_grammar=scale_matrix_ps_grammar,
    )

    m = Matrix(Int, "m")
    scale = Int("scale")
    driver.add_var_objects([m, scale])

    # Add preconditions
    driver.add_precondition(m.len() >= 1)
    driver.add_precondition(m[0].len() >= 1)

    driver.fns_synths = [outer_loop_index_first_synth]

    start_time = time.time()
    scale_matrix(m, scale)
    run_synthesis_algorithm(
        driver=driver,
        data_type=DataType.INT32,
        benchmark_name="scale_matrix",
        has_relaxed=False,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
