import argparse
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Matrix, Object, choose, ite
from metalift.vc_util import and_objects
from tests.llvm.hardlift.hardlift_common import (
    call_matrix_vec_mul,
    call_reduce_sum,
    call_vec_elemwise_mul,
    call_vec_scalar_mul,
    get_map_int_to_int_synth,
    get_matrix_or_vec_expr_eq_or_below_depth,
    get_no_arg_bool_fn,
    matrix_vec_mul,
    reduce_sum,
    vec_elemwise_mul,
    vec_scalar_mul,
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


def matmul_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        matrix_vec_mul,
        vec_elemwise_mul,
        vec_scalar_mul,
        reduce_sum,
        matrix_outer_loop_index_first_fn_decl,
        vector_outer_loop_index_fn_decl,
    ]


def matmul_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    ret_val = writes[0]
    weight, input = reads
    outer_loop_lower_bound = Int(0)
    outer_loop_upper_bound = weight.len()
    inner_loop_lower_bound = Int(0)
    inner_loop_upper_bound = input.len()
    if parser_args.relaxed:
        outer_loop_lower_bound = choose(
            outer_loop_lower_bound,
            outer_loop_lower_bound - 1,
            outer_loop_lower_bound + 1,
        )
        outer_loop_upper_bound = choose(
            outer_loop_upper_bound,
            outer_loop_upper_bound - 1,
            outer_loop_upper_bound + 1,
        )
        inner_loop_lower_bound = choose(
            inner_loop_lower_bound,
            inner_loop_lower_bound - 1,
            inner_loop_lower_bound + 1,
        )
        inner_loop_upper_bound = choose(
            inner_loop_upper_bound,
            inner_loop_upper_bound - 1,
            inner_loop_upper_bound + 1,
        )

    matrix = ite(
        is_matrix_outer_loop_index_first(),
        weight[outer_loop_lower_bound:outer_loop_upper_bound].col_slice(
            inner_loop_lower_bound, inner_loop_upper_bound
        ),
        weight[inner_loop_lower_bound:inner_loop_upper_bound].col_slice(
            outer_loop_lower_bound, outer_loop_upper_bound
        ),
    )
    matrix = choose(matrix, matrix.transpose())
    vec = ite(
        is_vector_outer_loop_index(),
        input[outer_loop_lower_bound:outer_loop_upper_bound],
        input[inner_loop_lower_bound:inner_loop_upper_bound],
    )
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
    inner_loop_lower_bound = Int(0)
    inner_loop_upper_bound = input.len()
    outer_loop_slice_upper_bound = row
    if parser_args.relaxed:
        outer_loop_lower_bound = choose(
            outer_loop_lower_bound,
            outer_loop_lower_bound - 1,
            outer_loop_lower_bound + 1,
        )
        outer_loop_upper_bound = choose(
            outer_loop_upper_bound,
            outer_loop_upper_bound - 1,
            outer_loop_upper_bound + 1,
        )
        inner_loop_lower_bound = choose(
            inner_loop_lower_bound,
            inner_loop_lower_bound - 1,
            inner_loop_lower_bound + 1,
        )
        inner_loop_upper_bound = choose(
            inner_loop_upper_bound,
            inner_loop_upper_bound - 1,
            inner_loop_upper_bound + 1,
        )
        outer_loop_slice_upper_bound = choose(
            outer_loop_slice_upper_bound,
            outer_loop_slice_upper_bound - 1,
            outer_loop_slice_upper_bound + 1,
        )
    matrix = ite(
        is_matrix_outer_loop_index_first(),
        weight[outer_loop_lower_bound:outer_loop_slice_upper_bound],
        weight[inner_loop_lower_bound:inner_loop_upper_bound].col_slice(
            outer_loop_lower_bound, outer_loop_slice_upper_bound
        ),
    )
    matrix = choose(matrix, matrix.transpose())
    vec = ite(
        is_vector_outer_loop_index(),
        input[outer_loop_lower_bound:outer_loop_slice_upper_bound],
        input[inner_loop_lower_bound:inner_loop_upper_bound],
    )
    vec = get_matrix_or_vec_expr_eq_or_below_depth(
        matrix_or_vec_var=vec,
        int_vars=[Int(0), Int(1)],
        depth=parser_args.depth,
        additional_matrix=matrix,
    )
    return and_objects(
        row >= outer_loop_lower_bound, row <= outer_loop_upper_bound, out == vec
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
    outer_loop_slice_upper_bound = row
    inner_loop_slice_upper_bound = col
    if parser_args.relaxed:
        outer_loop_lower_bound = choose(
            outer_loop_lower_bound,
            outer_loop_lower_bound - 1,
            outer_loop_lower_bound + 1,
        )
        outer_loop_upper_bound = choose(
            outer_loop_upper_bound,
            outer_loop_upper_bound - 1,
            outer_loop_upper_bound + 1,
        )
        inner_loop_lower_bound = choose(
            inner_loop_lower_bound,
            inner_loop_lower_bound - 1,
            inner_loop_lower_bound + 1,
        )
        inner_loop_upper_bound = choose(
            inner_loop_upper_bound,
            inner_loop_upper_bound - 1,
            inner_loop_upper_bound + 1,
        )
        outer_loop_slice_upper_bound = choose(
            outer_loop_slice_upper_bound,
            outer_loop_slice_upper_bound - 1,
            outer_loop_slice_upper_bound + 1,
        )
        inner_loop_slice_upper_bound = choose(
            inner_loop_slice_upper_bound,
            inner_loop_slice_upper_bound - 1,
            inner_loop_slice_upper_bound + 1,
        )
    outer_loop_matrix = ite(
        is_matrix_outer_loop_index_first(),
        weight[outer_loop_lower_bound:outer_loop_slice_upper_bound],
        weight[inner_loop_lower_bound:inner_loop_upper_bound].col_slice(
            outer_loop_lower_bound, outer_loop_slice_upper_bound
        ),
    )
    outer_loop_matrix = choose(outer_loop_matrix, outer_loop_matrix.transpose())
    outer_loop_vec = ite(
        is_vector_outer_loop_index(),
        input[outer_loop_lower_bound:outer_loop_slice_upper_bound],
        input[inner_loop_lower_bound:inner_loop_upper_bound],
    )

    inner_loop_weight_vec = ite(
        is_matrix_outer_loop_index_first(),
        weight[row][inner_loop_lower_bound:inner_loop_slice_upper_bound],
        weight[inner_loop_lower_bound:inner_loop_slice_upper_bound].col_vec(row),
    )
    inner_loop_vec_to_reduce = ite(
        is_vector_outer_loop_index(),
        call_vec_scalar_mul(input[row], inner_loop_weight_vec),
        call_vec_elemwise_mul(inner_loop_weight_vec, input[:col]),
    )

    return and_objects(
        row >= 0,
        row < weight.len(),
        col >= 0,
        col <= input.len(),
        curr == call_reduce_sum(inner_loop_vec_to_reduce),
        out == call_matrix_vec_mul(outer_loop_matrix, outer_loop_vec),
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int)
    parser.add_argument("--relaxed", action="store_true")
    parser_args = parser.parse_args()

    driver = Driver()
    matmul = driver.analyze(
        llvm_filepath="tests/llvm/hardlift/llama/cpp/matmul.ll",
        loops_filepath="tests/llvm/hardlift/llama/cpp/matmul.loops",
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
        matrix_outer_loop_index_first_synth,
        vector_outer_loop_index_synth,
    ]

    matmul(weight_var, input_var)

    relaxed_suffix = "_relaxed" if parser_args.relaxed else ""
    depth_suffix = f"_depth{parser_args.depth}"
    driver.synthesize(filename=f"matmul{depth_suffix}{relaxed_suffix}")
