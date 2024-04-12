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


def mat1x3_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        *vec_vec_to_vec_target_lang,
        *scalar_vec_to_vec_target_lang,
        *vec_to_vec_target_lang,
        *vec_to_int_target_lang,
        matrix_vec_mul,
    ]


def mat1x3_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    y = writes[0]
    N, h, x = reads
    int_var = choose(Int(0), N).maybe_relaxed(parser_args.relaxed)
    slice_index = get_int_expr_eq_or_below_depth(int_var, parser_args.depth)

    matrix = choose(h[slice_index:slice_index].col_slice(slice_index, slice_index))
    matrix = choose(matrix, matrix.transpose())
    vec = choose(x[slice_index:slice_index], matrix[slice_index])
    vec = get_matrix_or_vec_expr_eq_or_below_depth(
        matrix_or_vec_var=vec,
        int_var=int_var,
        depth=parser_args.depth,
        additional_matrix=matrix,
    )
    return y == vec


def mat1x3_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    N, h, x = reads
    y, f, i, sum = writes

    outer_loop_lower_bound = Int(0)
    outer_loop_upper_bound = N

    int_var = choose(Int(0), N, i).maybe_relaxed(parser_args.relaxed)
    slice_index = get_int_expr_eq_or_below_depth(int_var, parser_args.depth)

    matrix = choose(h[slice_index:slice_index].col_slice(slice_index, slice_index))
    matrix = choose(matrix, matrix.transpose())
    vec = choose(x[slice_index:slice_index], matrix[slice_index])
    vec = get_matrix_or_vec_expr_eq_or_below_depth(
        matrix_or_vec_var=vec,
        int_var=int_var,
        depth=parser_args.depth,
        additional_matrix=matrix,
    )
    return and_objects(
        i >= outer_loop_lower_bound.maybe_relaxed(parser_args.relaxed),
        i <= outer_loop_upper_bound.maybe_relaxed(parser_args.relaxed),
        y == vec,
    )


def mat1x3_inv1_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    f, sum = writes
    N, h, x = reads
    y, i = in_scope

    outer_loop_lower_bound = Int(0)
    outer_loop_upper_bound = N
    inner_loop_lower_bound = Int(0)
    inner_loop_upper_bound = N

    int_var = choose(Int(0), N, i, f).maybe_relaxed(parser_args.relaxed)
    slice_index = get_int_expr_eq_or_below_depth(int_var, parser_args.depth)

    matrix = h[slice_index:slice_index].col_slice(slice_index, slice_index)
    matrix = choose(matrix, matrix.transpose())
    vec = choose(x[slice_index:slice_index], matrix[slice_index])
    vec = get_matrix_or_vec_expr_eq_or_below_depth(
        matrix_or_vec_var=vec,
        int_var=int_var,
        depth=parser_args.depth,
        additional_matrix=matrix,
    )
    return and_objects(
        i >= outer_loop_lower_bound.maybe_relaxed(parser_args.relaxed),
        i < outer_loop_upper_bound.maybe_relaxed(parser_args.relaxed),
        f >= inner_loop_lower_bound.maybe_relaxed(parser_args.relaxed),
        f <= inner_loop_upper_bound.maybe_relaxed(parser_args.relaxed),
        sum == vec_to_int(vec),
        y == vec,
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int)
    parser.add_argument("--relaxed", action="store_true")
    parser_args = parser.parse_args()

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

    map_int_to_int_synth = get_map_int_to_int_synth()
    driver.fns_synths = [
        map_int_to_int_synth,
    ]

    mat1x3(N, h, x)

    start_time = time.time()
    relaxed_suffix = "_relaxed" if parser_args.relaxed else ""
    depth_suffix = f"_depth{parser_args.depth}"
    driver.synthesize(filename=f"mat1x3{depth_suffix}{relaxed_suffix}")
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
