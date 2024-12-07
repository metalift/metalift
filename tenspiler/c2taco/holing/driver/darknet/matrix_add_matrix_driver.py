import time
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int, Matrix, Object, choose, ite
from metalift.vc_util import and_objects
from tenspiler.axioms import matrix_elemwise_add_axiom, vec_elemwise_add_axiom
from tenspiler.codegen.utils import DataType
from tenspiler.tenspiler_common import (
    call_matrix_elemwise_add,
    call_vec_elemwise_add,
    get_no_arg_bool_fn,
    matrix_elemwise_add,
    vec_elemwise_add,
)
from tenspiler.utils.synthesis_utils import run_synthesis_algorithm

# Some loop functions
outer_loop_index_first_fn_name = "MATRIX_OUTER_LOOP_INDEX_FIRST"
(
    outer_loop_index_first_fn_decl,
    outer_loop_index_first_synth,
    is_outer_loop_index_first,
) = get_no_arg_bool_fn(outer_loop_index_first_fn_name)


def matrix_add_matrix_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        vec_elemwise_add,
        matrix_elemwise_add,
        outer_loop_index_first_fn_decl,
        vec_elemwise_add_axiom,
        matrix_elemwise_add_axiom,
    ]


def matrix_add_matrix_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    from_matrix, to_matrix = reads
    out, i, j, _, _ = writes
    matrix = choose(from_matrix, to_matrix)
    matrix = ite(
        is_outer_loop_index_first(),
        matrix[:i],
        matrix.col_slice(0, i),
    )
    matrix = choose(matrix, matrix.transpose())
    return and_objects(
        i >= 0, i <= from_matrix.len(), out == call_matrix_elemwise_add(matrix, matrix)
    )


def matrix_add_matrix_inv1_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    from_matrix, to_matrix = reads
    out, i = in_scope
    j, _, row_vec = writes
    matrix = choose(from_matrix, to_matrix)
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
        i < from_matrix.len(),
        j >= 0,
        j <= from_matrix[0].len(),
        row_vec == call_vec_elemwise_add(inner_loop_vec, inner_loop_vec),
        out == call_matrix_elemwise_add(outer_loop_matrix, outer_loop_matrix),
    )


def matrix_add_matrix_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    from_matrix, to_matrix = reads
    out = writes[0]
    matrix = choose(from_matrix, to_matrix)
    matrix = choose(matrix, matrix.transpose())
    return out == call_matrix_elemwise_add(matrix, matrix)


if __name__ == "__main__":
    driver = Driver()
    matrix_add_matrix = driver.analyze(
        llvm_filepath="tenspiler/c2taco/cpp/for_synthesis/darknet/matrix_add_matrix.ll",
        loops_filepath="tenspiler/c2taco/cpp/for_synthesis/darknet/matrix_add_matrix.loops",
        fn_name="matrix_add_matrix",
        target_lang_fn=matrix_add_matrix_target_lang,
        inv_grammars={
            "matrix_add_matrix_inv0": InvGrammar(matrix_add_matrix_inv0_grammar, []),
            "matrix_add_matrix_inv1": InvGrammar(
                matrix_add_matrix_inv1_grammar, ["i", "agg.result"]
            ),
        },
        ps_grammar=matrix_add_matrix_ps_grammar,
    )

    from_matrix = Matrix(Int, "from_matrix")
    to_matrix = Matrix(Int, "to_matrix")
    driver.add_var_objects([from_matrix, to_matrix])

    # Add preconditions
    driver.add_precondition(from_matrix.len() > 1)
    driver.add_precondition(from_matrix.len() == to_matrix.len())
    driver.add_precondition(from_matrix[0].len() == to_matrix[0].len())

    driver.fns_synths = [outer_loop_index_first_synth]

    start_time = time.time()
    matrix_add_matrix(from_matrix, to_matrix)
    run_synthesis_algorithm(
        driver=driver,
        data_type=DataType.INT32,
        benchmark_name="matrix_add_matrix",
        has_relaxed=False,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
