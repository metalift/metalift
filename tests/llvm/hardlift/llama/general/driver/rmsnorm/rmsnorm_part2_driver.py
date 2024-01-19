import argparse
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tests.llvm.hardlift.hardlift_common import (
    get_map_int_to_int_synth,
    get_matrix_or_vec_expr_eq_or_below_depth_with_sym_grammar,
    vec_elemwise_mul,
    vec_scalar_mul,
)


def rmsnorm_part2_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [vec_scalar_mul, vec_elemwise_mul]


def rmsnorm_part2_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    ret_val = writes[0]
    input, weight, ss = reads

    lower_bound = Int(0)
    upper_bound = input.len()
    if parser_args.relaxed:
        lower_bound = choose(lower_bound, lower_bound - 1, lower_bound + 1)
        upper_bound = choose(upper_bound, upper_bound - 1, upper_bound + 1)

    vec = choose(input[lower_bound:upper_bound], weight[lower_bound:upper_bound])
    return ret_val == get_matrix_or_vec_expr_eq_or_below_depth_with_sym_grammar(
        matrix_or_vec_var=vec,
        int_vars=[Int(1), ss, input.len()],
        depth=parser_args.depth,
    )


def rmsnorm_part2_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    # Second loop
    input, weight, ss = reads
    out = writes[0]
    i = writes[1]

    lower_bound = Int(0)
    upper_bound = input.len()
    slice_upper_bound = i
    if parser_args.relaxed:
        lower_bound = choose(lower_bound, lower_bound - 1, lower_bound + 1)
        upper_bound = choose(upper_bound, upper_bound - 1, upper_bound + 1)
        slice_upper_bound = choose(
            slice_upper_bound, slice_upper_bound - 1, slice_upper_bound + 1
        )
    vec = choose(
        input[lower_bound:slice_upper_bound], weight[lower_bound:slice_upper_bound]
    )
    return and_objects(
        i >= lower_bound,
        i <= upper_bound,
        out
        == get_matrix_or_vec_expr_eq_or_below_depth_with_sym_grammar(
            matrix_or_vec_var=vec,
            int_vars=[Int(1), ss, input.len()],
            depth=parser_args.depth,
        ),
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int)
    parser.add_argument("--relaxed", action="store_true")
    parser_args = parser.parse_args()

    # Synthesize the second loop
    driver = Driver()
    rmsnorm_part2 = driver.analyze(
        llvm_filepath="tests/llvm/hardlift/llama/cpp/rmsnorm/rmsnorm_part2.ll",
        loops_filepath="tests/llvm/hardlift/llama/cpp/rmsnorm/rmsnorm_part2.loops",
        fn_name="rmsnorm_part2",
        target_lang_fn=rmsnorm_part2_target_lang,
        inv_grammars={
            "rmsnorm_part2_inv0": InvGrammar(rmsnorm_part2_inv0_grammar, []),
        },
        ps_grammar=rmsnorm_part2_ps_grammar,
    )

    input_var = mlList(Int, "input")
    weight_var = mlList(Int, "weight")
    ss = Int("ss")
    driver.add_var_objects([input_var, weight_var, ss])
    driver.add_precondition(input_var.len() == weight_var.len())
    driver.add_precondition(input_var.len() > 0)

    rmsnorm_part2(input_var, weight_var, ss)
    map_int_to_int_synth = get_map_int_to_int_synth()
    driver.fns_synths = [map_int_to_int_synth]

    relaxed_suffix = "_relaxed" if parser_args.relaxed else ""
    depth_suffix = f"_depth{parser_args.depth}"
    driver.synthesize(filename=f"rmsnorm_part2{depth_suffix}{relaxed_suffix}")
