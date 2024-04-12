import argparse
import time
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Matrix, Object, choose
from metalift.vc_util import and_objects
from tenspiler.tenspiler_common import (
    get_int_expr_eq_or_below_depth,
    get_map_int_to_int_synth,
    get_matrix_or_vec_expr_eq_or_below_depth,
    matrix_vec_mul,
    scalar_vec_to_vec_target_lang,
    vec_to_int,
    vec_to_int_target_lang,
    vec_to_vec_target_lang,
    vec_vec_to_vec_target_lang,
)


def gemv_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        *vec_vec_to_vec_target_lang,
        *scalar_vec_to_vec_target_lang,
        *vec_to_vec_target_lang,
        *vec_to_int_target_lang,
        matrix_vec_mul,
    ]


def gemv_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    y = writes[0]
    M, N, A, x = reads
    slice_index = choose(Int(0), Int(1), M, N).maybe_relaxed(parser_args.relaxed)
    slice_index = get_int_expr_eq_or_below_depth(slice_index, parser_args.depth)

    matrix = choose(A[slice_index:slice_index].col_slice(slice_index, slice_index))
    matrix = choose(matrix, matrix.transpose())
    vec = choose(x[slice_index:slice_index], matrix[slice_index])
    vec = get_matrix_or_vec_expr_eq_or_below_depth(
        matrix_or_vec_var=vec,
        int_vars=[Int(0), Int(1)],
        depth=parser_args.depth,
        additional_matrix=matrix,
    )
    return y == vec


def gemv_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    M, N, A, x = reads
    y, i, j, sum = writes

    outer_loop_lower_bound = Int(0)
    outer_loop_upper_bound = M

    int_var = choose(Int(0), M, N, i).maybe_relaxed(parser_args.relaxed)
    int_expr = get_int_expr_eq_or_below_depth(int_var, parser_args.depth)

    matrix = choose(A[int_expr:int_expr].col_slice(int_expr, int_expr))
    matrix = choose(matrix, matrix.transpose())
    vec = choose(x[int_expr:int_expr], matrix[int_expr])
    vec = get_matrix_or_vec_expr_eq_or_below_depth(
        matrix_or_vec_var=vec,
        int_vars=int_var,
        depth=parser_args.depth,
        additional_matrix=matrix,
    )
    return and_objects(
        i >= outer_loop_lower_bound.maybe_relaxed(parser_args.relaxed),
        i <= outer_loop_upper_bound.maybe_relaxed(parser_args.relaxed),
        y == vec,
    )


def gemv_inv1_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    j, sum = writes
    M, N, A, x = reads
    y, i = in_scope

    outer_loop_lower_bound = Int(0)
    outer_loop_upper_bound = M
    inner_loop_lower_bound = Int(0)
    inner_loop_upper_bound = N

    slice_index = choose(Int(0), M, N, i, j).maybe_relaxed(parser_args.relaxed)
    slice_index = get_int_expr_eq_or_below_depth(slice_index, parser_args.depth)

    matrix = A[slice_index:slice_index].col_slice(slice_index, slice_index)
    matrix = choose(matrix, matrix.transpose())
    vec = choose(x[slice_index:slice_index], matrix[slice_index])
    vec = get_matrix_or_vec_expr_eq_or_below_depth(
        matrix_or_vec_var=vec,
        int_vars=[Int(0), Int(1)],
        depth=parser_args.depth,
        additional_matrix=matrix,
    )
    return and_objects(
        i >= outer_loop_lower_bound.maybe_relaxed(parser_args.relaxed),
        i < outer_loop_upper_bound.maybe_relaxed(parser_args.relaxed),
        j >= inner_loop_lower_bound.maybe_relaxed(parser_args.relaxed),
        j <= inner_loop_upper_bound.maybe_relaxed(parser_args.relaxed),
        sum == vec_to_int(vec),
        y == vec,
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int)
    parser.add_argument("--relaxed", action="store_true")
    parser_args = parser.parse_args()

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

    map_int_to_int_synth = get_map_int_to_int_synth()
    driver.fns_synths = [
        map_int_to_int_synth,
    ]

    gemv(M, N, A, x)

    start_time = time.time()
    relaxed_suffix = "_relaxed" if parser_args.relaxed else ""
    depth_suffix = f"_depth{parser_args.depth}"
    driver.synthesize(filename=f"gemv{depth_suffix}{relaxed_suffix}")
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
