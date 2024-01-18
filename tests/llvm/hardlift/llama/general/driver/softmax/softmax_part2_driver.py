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


def softmax_part2_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        *vec_vec_to_vec_target_lang,
        *scalar_vec_to_vec_target_lang,
        *vec_to_vec_target_lang,
    ]


def softmax_part2_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    ret_val = writes[0]
    input, max_pos, max_val = reads
    vec = choose(input[:max_pos])
    return ret_val == get_matrix_or_vec_expr_eq_or_below_depth(
        matrix_or_vec_var=vec, int_vars=[max_val, max_pos], depth=parser_args.depth
    )


def softmax_part2_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    input, max_pos, max_val = reads
    out, cur, i = writes
    int_var = choose(max_pos, max_val)
    vec = choose(input[:i])

    return and_objects(
        i >= 0,
        i <= max_pos,
        out
        == get_matrix_or_vec_expr_eq_or_below_depth(
            matrix_or_vec_var=vec, int_vars=[max_val, max_pos], depth=parser_args.depth
        ),
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int)
    parser_args = parser.parse_args()

    # Synthesize part 2
    driver = Driver()
    softmax_part2 = driver.analyze(
        llvm_filepath="tests/llvm/hardlift/llama/cpp/softmax/softmax_part2.ll",
        loops_filepath="tests/llvm/hardlift/llama/cpp/softmax/softmax_part2.loops",
        fn_name="softmax_part2",
        target_lang_fn=softmax_part2_target_lang,
        inv_grammars={
            "softmax_part2_inv0": InvGrammar(softmax_part2_inv0_grammar, []),
        },
        ps_grammar=softmax_part2_ps_grammar,
    )

    input_var = mlList(Int, "input")
    max_pos_var = Int("max_pos")
    max_val_var = Int("max_val")
    driver.add_var_objects([input_var, max_pos_var, max_val_var])
    driver.add_precondition(input_var.len() > 0)
    driver.add_precondition(max_pos_var <= input_var.len())
    driver.add_precondition(max_pos_var >= 1)

    softmax_part2(input_var, max_pos_var, max_val_var)
    map_int_to_int_synth = get_map_int_to_int_synth()
    driver.fns_synths = [map_int_to_int_synth]
    driver.synthesize()
