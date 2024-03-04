import argparse
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tenspiler.tenspiler_common import call_reduce_max, reduce_max


def softmax_part1_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [reduce_max]


def softmax_part1_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    ret_val = writes[0]
    input, max_pos = reads
    vec = choose(input[1:max_pos])
    return ret_val == call_reduce_max(vec)


def softmax_part1_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    input, max_pos = reads
    i, max_val = writes
    vec = input[1:i]
    return and_objects(i >= 1, i <= max_pos, max_val == call_reduce_max(vec))


def softmax_part1_relaxed_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    ret_val = writes[0]
    input, max_pos = reads
    lower_bound = choose(Int(0), Int(1), Int(2))
    upper_bound = choose(max_pos, max_pos - 1, max_pos + 1)
    vec = input[lower_bound:upper_bound]
    return ret_val == call_reduce_max(vec)


def softmax_part1_relaxed_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    input, max_pos = reads
    i, max_val = writes
    lower_bound = choose(Int(0), Int(1), Int(2))
    upper_bound = choose(max_pos, max_pos - 1, max_pos + 1)
    vec = input[lower_bound:i]
    return and_objects(
        i >= lower_bound, i <= upper_bound, max_val == call_reduce_max(vec)
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--relaxed", action="store_true")
    parser_args = parser.parse_args()
    if parser_args.relaxed:
        inv0_grammar_fn = softmax_part1_relaxed_inv0_grammar
        ps_grammar_fn = softmax_part1_relaxed_ps_grammar
    else:
        inv0_grammar_fn = softmax_part1_inv0_grammar
        ps_grammar_fn = softmax_part1_ps_grammar

    # Synthesize part 1
    driver = Driver()
    softmax_part1 = driver.analyze(
        llvm_filepath="tenspiler/llama/cpp/for_synthesis/softmax/softmax_part1.ll",
        loops_filepath="tenspiler/llama/cpp/for_synthesis/softmax/softmax_part1.loops",
        fn_name="softmax_part1",
        target_lang_fn=softmax_part1_target_lang,
        inv_grammars={
            "softmax_part1_inv0": InvGrammar(inv0_grammar_fn, []),
        },
        ps_grammar=ps_grammar_fn,
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
