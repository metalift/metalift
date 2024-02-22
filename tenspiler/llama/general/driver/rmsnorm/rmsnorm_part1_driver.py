import argparse
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tenspiler.tenspiler_common import (
    get_int_expr_eq_or_below_depth,
    get_map_int_to_int_synth,
    get_matrix_or_vec_expr_eq_or_below_depth,
    scalar_vec_to_vec_target_lang,
    vec_to_int,
    vec_to_int_target_lang,
    vec_to_vec_target_lang,
    vec_vec_to_vec_target_lang,
)


def rmsnorm_part1_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        *vec_vec_to_vec_target_lang,
        *scalar_vec_to_vec_target_lang,
        *vec_to_vec_target_lang,
        *vec_to_int_target_lang,
    ]


def rmsnorm_part1_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    ret_val = writes[0]
    input, weight = reads
    lower_bound = Int(0)
    upper_bound = input.len()
    slice_index = choose(lower_bound, upper_bound, Int(1)).maybe_relaxed(
        parser_args.relaxed
    )
    slice_index = get_int_expr_eq_or_below_depth(slice_index, depth=parser_args.depth)
    vec = choose(input[slice_index:slice_index], weight[slice_index:slice_index])
    vec = get_matrix_or_vec_expr_eq_or_below_depth(
        matrix_or_vec_var=vec, int_vars=[Int(0), Int(1)], depth=parser_args.depth
    )
    return ret_val == vec_to_int(vec)


def rmsnorm_part1_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    # First loop
    input, weight = reads
    i, ss = writes

    lower_bound = Int(0)
    upper_bound = input.len()
    slice_index = choose(lower_bound, upper_bound, i, Int(1)).maybe_relaxed(
        parser_args.relaxed
    )
    slice_index = get_int_expr_eq_or_below_depth(slice_index, depth=parser_args.depth)
    vec = choose(input[slice_index:slice_index], weight[slice_index:slice_index])
    vec = get_matrix_or_vec_expr_eq_or_below_depth(
        matrix_or_vec_var=vec, int_vars=[Int(0), Int(1)], depth=parser_args.depth
    )

    return and_objects(
        i >= lower_bound.maybe_relaxed(parser_args.relaxed),
        i <= upper_bound.maybe_relaxed(parser_args.relaxed),
        ss == vec_to_int(vec),
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int)
    parser.add_argument("--relaxed", action="store_true")
    parser_args = parser.parse_args()

    # Synthesize the first loop
    driver = Driver()
    rmsnorm_part1 = driver.analyze(
        llvm_filepath="tenspiler/llama/cpp/rmsnorm/rmsnorm/rmsnorm_part1.ll",
        loops_filepath="tenspiler/llama/cpp/rmsnorm/rmsnorm/rmsnorm_part1.loops",
        fn_name="rmsnorm_part1",
        target_lang_fn=rmsnorm_part1_target_lang,
        inv_grammars={
            "rmsnorm_part1_inv0": InvGrammar(rmsnorm_part1_inv0_grammar, []),
        },
        ps_grammar=rmsnorm_part1_ps_grammar,
    )

    input_var = mlList(Int, "input")
    weight_var = mlList(Int, "weight")
    driver.add_var_objects([input_var, weight_var])
    driver.add_precondition(input_var.len() == weight_var.len())
    driver.add_precondition(input_var.len() > 0)

    rmsnorm_part1(input_var, weight_var)
    map_int_to_int_synth = get_map_int_to_int_synth()
    driver.fns_synths = [map_int_to_int_synth]

    relaxed_suffix = "_relaxed" if parser_args.relaxed else ""
    depth_suffix = f"_depth{parser_args.depth}"
    driver.synthesize(filename=f"rmsnorm_part1{depth_suffix}{relaxed_suffix}")
