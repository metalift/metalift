import argparse
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tests.llvm.hardlift.hardlift_common import vec_to_int, vec_to_int_target_lang


def softmax_part1_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return vec_to_int_target_lang


def softmax_part1_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    ret_val = writes[0]
    input, max_pos = reads
    lower_bound = Int(1)
    upper_bound = max_pos
    if parser_args.relaxed:
        lower_bound = choose(lower_bound, lower_bound - 1, lower_bound + 1)
        upper_bound = choose(upper_bound, upper_bound - 1, upper_bound + 1)
    vec = choose(input[lower_bound:upper_bound])
    return ret_val == vec_to_int(vec)


def softmax_part1_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    input, max_pos = reads
    i, max_val = writes
    lower_bound = Int(1)
    upper_bound = max_pos
    slice_upper_bound = i
    if parser_args.relaxed:
        lower_bound = choose(lower_bound, lower_bound - 1, lower_bound + 1)
        upper_bound = choose(upper_bound, upper_bound - 1, upper_bound + 1)
        slice_upper_bound = choose(
            slice_upper_bound, slice_upper_bound - 1, slice_upper_bound + 1
        )
    vec = input[lower_bound:slice_upper_bound]
    return and_objects(i >= lower_bound, i <= upper_bound, max_val == vec_to_int(vec))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--relaxed", action="store_true")
    parser_args = parser.parse_args()

    # Synthesize part 1
    driver = Driver()
    softmax_part1 = driver.analyze(
        llvm_filepath="tests/llvm/hardlift/llama/cpp/softmax/softmax_part1.ll",
        loops_filepath="tests/llvm/hardlift/llama/cpp/softmax/softmax_part1.loops",
        fn_name="softmax_part1",
        target_lang_fn=softmax_part1_target_lang,
        inv_grammars={
            "softmax_part1_inv0": InvGrammar(softmax_part1_inv0_grammar, []),
        },
        ps_grammar=softmax_part1_ps_grammar,
    )

    input_var = mlList(Int, "input")
    max_pos_var = Int("max_pos")
    driver.add_var_objects([input_var, max_pos_var])
    driver.add_precondition(input_var.len() > 0)
    driver.add_precondition(max_pos_var <= input_var.len())
    driver.add_precondition(max_pos_var >= 1)

    softmax_part1(input_var, max_pos_var)
    relaxed_suffix = "_relaxed" if parser_args.relaxed else ""
    driver.synthesize(filename=f"softmax_part1{relaxed_suffix}")
