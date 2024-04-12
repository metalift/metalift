import argparse
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tenspiler.tenspiler_common import (
    get_int_expr_eq_or_below_depth,
    get_matrix_or_vec_expr_eq_or_below_depth,
    scalar_vec_to_vec_target_lang,
    vec_to_int,
    vec_to_vec_target_lang,
    vec_vec_to_vec_target_lang,
)


def mag_array_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        *vec_vec_to_vec_target_lang,
        *scalar_vec_to_vec_target_lang,
        *vec_to_vec_target_lang,
    ]


def mag_array_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    a, n = reads
    sum = writes[0]
    lower_bound = Int(0)
    upper_bound = n
    slice_index = choose(lower_bound, upper_bound, Int(1)).maybe_relaxed(
        parser_args.relaxed
    )
    slice_index = get_int_expr_eq_or_below_depth(slice_index, depth=parser_args.depth)
    vec = choose(a[slice_index:slice_index])
    vec = get_matrix_or_vec_expr_eq_or_below_depth(
        vec, int_vars=[n], depth=parser_args.depth
    )
    return sum == vec_to_int(vec)


def mag_array_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    output, max_pos = reads
    i, sum = writes
    lower_bound = Int(0)
    upper_bound = max_pos
    slice_index = choose(lower_bound, upper_bound, i).maybe_relaxed(parser_args.relaxed)
    vec = output[slice_index:slice_index]

    return and_objects(
        i >= lower_bound.maybe_relaxed(parser_args.relaxed),
        i <= upper_bound.maybe_relaxed(parser_args.relaxed),
        sum == vec_to_int(vec),
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int)
    parser.add_argument("--relaxed", action="store_true")
    parser_args = parser.parse_args()

    # Synthesize part 3
    driver = Driver()
    mag_array = driver.analyze(
        llvm_filepath="tenspiler/llama/cpp/for_synthesis/softmax/mag_array.ll",
        loops_filepath="tenspiler/llama/cpp/for_synthesis/softmax/mag_array.loops",
        fn_name="mag_array",
        target_lang_fn=mag_array_target_lang,
        inv_grammars={
            "mag_array_inv0": InvGrammar(mag_array_inv0_grammar, []),
        },
        ps_grammar=mag_array_ps_grammar,
    )

    output_var = mlList(Int, "output")
    max_pos_var = Int("max_pos")
    driver.add_var_objects([output_var, max_pos_var])
    driver.add_precondition(output_var.len() > 0)
    driver.add_precondition(max_pos_var <= output_var.len())
    driver.add_precondition(max_pos_var >= 1)

    mag_array(output_var, max_pos_var)

    relaxed_suffix = "_relaxed" if parser_args.relaxed else ""
    depth_suffix = f"_depth{parser_args.depth}"
    driver.synthesize(filename=f"mag_array{depth_suffix}{relaxed_suffix}")
