import argparse
import time
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int, Matrix, Object, choose
from metalift.vc_util import and_objects
from tenspiler.tenspiler_common import (
    get_int_expr_eq_or_below_depth,
    get_map_int_to_int_synth,
    get_matrix_or_vec_expr_eq_or_below_depth,
    matrix_matrix_to_matrix_target_lang,
    matrix_vec_mul,
    reduce_sum,
    scalar_matrix_to_matrix_target_lang,
    scalar_vec_to_vec_target_lang,
    vec_to_vec_target_lang,
    vec_vec_to_vec_target_lang,
)


def matscal_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        matrix_vec_mul,
        reduce_sum,
        *vec_to_vec_target_lang,
        *scalar_vec_to_vec_target_lang,
        *scalar_matrix_to_matrix_target_lang,
        *vec_vec_to_vec_target_lang,
        *matrix_matrix_to_matrix_target_lang,
    ]


def matscal_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    mat, val, m, n = reads
    out, i, j, _, _ = writes
    lower_bound, upper_bound = Int(0), m
    int_var = choose(Int(0), m, n, i, val).maybe_relaxed(parser_args.relaxed)
    slice_index = get_int_expr_eq_or_below_depth(int_var, parser_args.depth)
    matrix = mat[slice_index:slice_index].col_slice(slice_index, slice_index)
    matrix = choose(matrix, matrix.transpose())
    return and_objects(
        i >= lower_bound.maybe_relaxed(parser_args.relaxed),
        i <= upper_bound.maybe_relaxed(parser_args.relaxed),
        out
        == get_matrix_or_vec_expr_eq_or_below_depth(
            matrix_or_vec_var=matrix,
            int_var=int_var,
            depth=parser_args.depth,
        ),
    )


def matscal_inv1_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    mat, val, m, n = reads
    out, i = in_scope
    j, _, row_vec = writes
    int_var = choose(Int(0), m, n, i, j, val).maybe_relaxed(parser_args.relaxed)
    slice_index = get_int_expr_eq_or_below_depth(int_var, parser_args.depth)
    matrix = mat[slice_index:slice_index].col_slice(slice_index, slice_index)
    matrix = choose(matrix, matrix.transpose())
    vec = matrix[slice_index]

    outer_loop_lower_bound, outer_loop_upper_bound = Int(0), m
    inner_loop_lower_bound, inner_loop_upper_bound = Int(0), n
    return and_objects(
        i >= outer_loop_lower_bound.maybe_relaxed(parser_args.relaxed),
        i < outer_loop_upper_bound.maybe_relaxed(parser_args.relaxed),
        j >= inner_loop_lower_bound.maybe_relaxed(parser_args.relaxed),
        j <= inner_loop_upper_bound.maybe_relaxed(parser_args.relaxed),
        row_vec
        == get_matrix_or_vec_expr_eq_or_below_depth(
            matrix_or_vec_var=vec,
            int_var=int_var,
            depth=parser_args.depth,
            additional_matrix=matrix,
        ),
        out
        == get_matrix_or_vec_expr_eq_or_below_depth(
            matrix_or_vec_var=matrix, int_var=int_var, depth=parser_args.depth
        ),
    )


def matscal_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    mat, val, m, n = reads
    out = writes[0]
    int_var = choose(Int(0), m, n, val).maybe_relaxed(parser_args.relaxed)
    slice_index = get_int_expr_eq_or_below_depth(int_var, parser_args.depth)
    matrix = mat[slice_index:slice_index].col_slice(slice_index, slice_index)
    matrix = choose(matrix, matrix.transpose())
    return out == get_matrix_or_vec_expr_eq_or_below_depth(
        matrix_or_vec_var=matrix, int_var=int_var, depth=parser_args.depth
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int)
    parser.add_argument("--relaxed", action="store_true")
    parser_args = parser.parse_args()

    driver = Driver()
    matscal = driver.analyze(
        llvm_filepath="tenspiler/c2taco/cpp/for_synthesis/dsp/matscal.ll",
        loops_filepath="tenspiler/c2taco/cpp/for_synthesis/dsp/matscal.loops",
        fn_name="matscal",
        target_lang_fn=matscal_target_lang,
        inv_grammars={
            "matscal_inv0": InvGrammar(matscal_inv0_grammar, []),
            "matscal_inv1": InvGrammar(matscal_inv1_grammar, ["i", "agg.result"]),
        },
        ps_grammar=matscal_ps_grammar,
    )

    mat = Matrix(Int, "mat")
    val = Int("val")
    m = Int("m")
    n = Int("n")
    driver.add_var_objects([mat, val, m, n])

    # Add preconditions
    driver.add_precondition(m >= 1)
    driver.add_precondition(n >= 1)
    driver.add_precondition(mat.len() >= m)
    driver.add_precondition(mat[0].len() >= n)

    map_int_to_int_synth = get_map_int_to_int_synth()
    driver.fns_synths = [
        map_int_to_int_synth,
    ]

    matscal(mat, val, m, n)

    start_time = time.time()
    relaxed_suffix = "_relaxed" if parser_args.relaxed else ""
    depth_suffix = f"_depth{parser_args.depth}"
    driver.synthesize(filename=f"matscal{depth_suffix}{relaxed_suffix}", no_verify=True)
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
