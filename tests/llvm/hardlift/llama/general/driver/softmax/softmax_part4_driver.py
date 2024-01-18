import argparse
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tests.llvm.hardlift.hardlift_common import (
    get_map_int_to_int_synth,
    get_matrix_or_vec_expr_eq_or_below_depth,
    scalar_vec_to_vec_target_lang,
    vec_to_vec_target_lang,
    vec_vec_to_vec_target_lang,
)


def softmax_part4_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        *vec_vec_to_vec_target_lang,
        *scalar_vec_to_vec_target_lang,
        *vec_to_vec_target_lang,
    ]


def softmax_part4_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    ret_val = writes[0]
    unnormalized_output, max_pos, sum = reads
    lower_bound = Int(0)
    upper_bound = max_pos
    if parser_args.relaxed:
        lower_bound = choose(lower_bound, lower_bound - 1, lower_bound + 1)
        upper_bound = choose(upper_bound, upper_bound - 1, upper_bound + 1)
    vec = choose(unnormalized_output[lower_bound:upper_bound])
    return ret_val == get_matrix_or_vec_expr_eq_or_below_depth(
        matrix_or_vec_var=vec, int_vars=[sum, max_pos], depth=parser_args.depth
    )


def softmax_part4_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    unnormalized_output, max_pos, sum = reads
    out, i, _ = writes

    lower_bound = Int(0)
    upper_bound = max_pos
    slice_upper_bound = i
    if parser_args.relaxed:
        lower_bound = choose(lower_bound, lower_bound - 1, lower_bound + 1)
        upper_bound = choose(upper_bound, upper_bound - 1, upper_bound + 1)
        slice_upper_bound = choose(
            slice_upper_bound, slice_upper_bound - 1, slice_upper_bound + 1
        )

    vec = choose(unnormalized_output[lower_bound:slice_upper_bound])

    return and_objects(
        i >= lower_bound,
        i <= upper_bound,
        out
        == get_matrix_or_vec_expr_eq_or_below_depth(
            matrix_or_vec_var=vec, int_vars=[sum, max_pos], depth=parser_args.depth
        ),
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int)
    parser.add_argument("--relaxed", action="store_true")
    parser_args = parser.parse_args()
    # Synthesize part 4
    driver = Driver()
    softmax_part4 = driver.analyze(
        llvm_filepath="tests/llvm/hardlift/llama/cpp/softmax/softmax_part4.ll",
        loops_filepath="tests/llvm/hardlift/llama/cpp/softmax/softmax_part4.loops",
        fn_name="softmax_part4",
        target_lang_fn=softmax_part4_target_lang,
        inv_grammars={
            "softmax_part4_inv0": InvGrammar(softmax_part4_inv0_grammar, []),
        },
        ps_grammar=softmax_part4_ps_grammar,
    )

    unnormalized_output_var = mlList(Int, "unnormalized_output")
    max_pos_var = Int("max_pos")
    sum_var = Int("sum")
    driver.add_var_objects([unnormalized_output_var, max_pos_var, sum_var])
    driver.add_precondition(unnormalized_output_var.len() > 0)
    driver.add_precondition(max_pos_var <= unnormalized_output_var.len())
    driver.add_precondition(max_pos_var >= 1)

    softmax_part4(unnormalized_output_var, max_pos_var, sum_var)
    map_int_to_int_synth = get_map_int_to_int_synth()
    driver.fns_synths = [map_int_to_int_synth]

    relaxed_suffix = "_relaxed" if parser_args.relaxed else ""
    depth_suffix = f"_depth{parser_args.depth}"
    driver.synthesize(filename=f"softmax_part4{depth_suffix}{relaxed_suffix}")
