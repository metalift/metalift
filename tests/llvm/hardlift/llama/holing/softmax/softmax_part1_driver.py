from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int, fn_decl
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tests.llvm.hardlift.hardlift_common import (vec_to_int,
                                           scalar_vec_to_vec, call_vec_map, get_map_int_to_int_synth,
                                           map_int_to_int,
                                           map_int_to_int_fn_obj, reduce_max,
                                           reduce_mul, reduce_sum, vec_map,
                                           vec_scalar_add, vec_scalar_div,
                                           vec_scalar_mul, vec_scalar_sub, scalar_vec_to_vec_target_lang, vec_to_vec_target_lang)


def softmax_part1_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [reduce_max]

def softmax_part1_ps_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    ret_val = writes[0]
    input, max_pos = reads
    vec = choose(input[:max_pos])
    return ret_val == vec_to_int(vec)

def softmax_part1_inv0_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    input, max_pos = reads
    i, max_val = writes
    vec = choose(input, input[:i])
    lower_bound = choose(Int(0), Int(1))
    i_upper_bound = choose(max_pos, input.len())

    return and_objects(
        i >= i_lower_bound,
        i <= i_upper_bound,
        max_val == vec_to_int(vec)
    )

def softmax_part1_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        reduce_sum,
        reduce_mul,
        reduce_max
    ]


if __name__ == "__main__":
    # Synthesize part 1
    driver = Driver()
    softmax_part1 = driver.analyze(
        llvm_filepath="tests/llvm/gaudi/softmax_part1.ll",
        loops_filepath="tests/llvm/gaudi/softmax_part1.loops",
        fn_name="softmax_part1",
        target_lang_fn=softmax_part1_target_lang,
        inv_grammars={
            "softmax_part1_inv0": InvGrammar(softmax_part1_inv0_grammar, []),
        },
        ps_grammar=softmax_part1_ps_grammar
    )

    input_var = mlList(Int, "input")
    max_pos_var = Int("max_pos")
    driver.add_var_objects([input_var, max_pos_var])
    driver.add_precondition(input_var.len() > 0)
    driver.add_precondition(max_pos_var <= input_var.len())
    driver.add_precondition(max_pos_var >= 1)

    softmax_part1(input_var, max_pos_var)
    driver.synthesize(noVerify=True)
