import argparse
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


def matmul_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        *vec_vec_to_vec_target_lang,
        *scalar_vec_to_vec_target_lang,
        *vec_to_vec_target_lang,
        *vec_to_int_target_lang,
        matrix_vec_mul,
    ]


def matmul_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    ret_val = writes[0]
    weight, input = reads
    slice_index = choose(Int(0), weight.len(), input.len()).maybe_relaxed(
        parser_args.relaxed
    )
    slice_index = get_int_expr_eq_or_below_depth(slice_index, parser_args.depth)

    matrix = weight[slice_index:slice_index].col_slice(slice_index, slice_index)
    matrix = choose(matrix, matrix.transpose())
    vec = choose(input[slice_index:slice_index], matrix[slice_index])
    vec = get_matrix_or_vec_expr_eq_or_below_depth(
        matrix_or_vec_var=vec,
        int_vars=[Int(0), Int(1)],
        depth=parser_args.depth,
        additional_matrix=matrix,
    )
    return ret_val == vec


def matmul_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    weight, input = reads
    out, col, _, row = writes

    outer_loop_lower_bound = Int(0)
    outer_loop_upper_bound = weight.len()

    slice_index = choose(Int(0), row, weight.len(), input.len()).maybe_relaxed(
        parser_args.relaxed
    )
    slice_index = get_int_expr_eq_or_below_depth(slice_index, parser_args.depth)

    matrix = weight[slice_index:slice_index].col_slice(slice_index, slice_index)
    matrix = choose(matrix, matrix.transpose())
    vec = choose(input[slice_index:slice_index], matrix[slice_index])
    vec = get_matrix_or_vec_expr_eq_or_below_depth(
        matrix_or_vec_var=vec,
        int_vars=[Int(0), Int(1)],
        depth=parser_args.depth,
        additional_matrix=matrix,
    )
    return and_objects(
        row >= outer_loop_lower_bound.maybe_relaxed(parser_args.relaxed),
        row <= outer_loop_upper_bound.maybe_relaxed(parser_args.relaxed),
        out == vec,
    )


def matmul_inv1_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    col, curr = writes
    weight, input = reads
    out, row = in_scope
    outer_loop_lower_bound = Int(0)
    outer_loop_upper_bound = weight.len()
    inner_loop_lower_bound = Int(0)
    inner_loop_upper_bound = input.len()

    slice_index = choose(Int(0), row, weight.len(), input.len()).maybe_relaxed(
        parser_args.relaxed
    )
    slice_index = get_int_expr_eq_or_below_depth(slice_index, parser_args.depth)

    matrix = weight[slice_index:slice_index].col_slice(slice_index, slice_index)
    matrix = choose(matrix, matrix.transpose())
    vec = choose(input[slice_index:slice_index], matrix[slice_index])
    vec = get_matrix_or_vec_expr_eq_or_below_depth(
        matrix_or_vec_var=vec,
        int_vars=[Int(0), Int(1)],
        depth=parser_args.depth,
        additional_matrix=matrix,
    )
    return and_objects(
        row >= outer_loop_lower_bound.maybe_relaxed(parser_args.relaxed),
        row < outer_loop_upper_bound.maybe_relaxed(parser_args.relaxed),
        col >= inner_loop_lower_bound.maybe_relaxed(parser_args.relaxed),
        col <= inner_loop_upper_bound.maybe_relaxed(parser_args.relaxed),
        curr == vec_to_int(vec),
        out == vec,
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int)
    parser.add_argument("--relaxed", action="store_true")
    parser_args = parser.parse_args()

    driver = Driver()
    matmul = driver.analyze(
        llvm_filepath="tenspiler/llama/cpp/matmul.ll",
        loops_filepath="tenspiler/llama/cpp/matmul.loops",
        fn_name="matmul",
        target_lang_fn=matmul_target_lang,
        inv_grammars={
            "matmul_inv0": InvGrammar(matmul_inv0_grammar, []),
            "matmul_inv1": InvGrammar(matmul_inv1_grammar, ["row", "agg.result"]),
        },
        ps_grammar=matmul_ps_grammar,
    )

    weight_var = Matrix(Int, "weight")
    input_var = mlList(Int, "input")
    driver.add_var_objects([weight_var, input_var])
    driver.add_precondition(weight_var.len() > 0)
    driver.add_precondition(weight_var[0].len() > 0)
    driver.add_precondition(weight_var[0].len() == input_var.len())
    map_int_to_int_synth = get_map_int_to_int_synth()
    driver.fns_synths = [
        map_int_to_int_synth,
    ]

    matmul(weight_var, input_var)

    relaxed_suffix = "_relaxed" if parser_args.relaxed else ""
    depth_suffix = f"_depth{parser_args.depth}"
    driver.synthesize(filename=f"matmul{depth_suffix}{relaxed_suffix}")
