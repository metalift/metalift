from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int, ite
from metalift.ir import List as mlList
from metalift.ir import Object, call, choose, fn_decl
from metalift.vc_util import and_objects
from tests.llvm.gaudi.gaudi_common import (an_arr2_to_arr, an_arr_to_int,
                                           an_int_and_arr_to_arr, call_reduce_max, call_vec_map_exp, call_vec_scalar_add, reduce_mul,
                                           reduce_sum, vec_elemwise_add,
                                           vec_elemwise_mul, vec_scalar_add, an_arr_to_arr,
                                           vec_scalar_mul, reduce_max, exp, vec_exp_map, EXP_FN_NAME)
from tests.python.utils.utils import codegen

def softmax_part1_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        reduce_sum,
        reduce_mul,
        reduce_max
    ]

def softmax_part1_ps_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    ret_val = writes[0]
    input, max_pos = reads
    vec = choose(input, input[:max_pos])
    return ret_val == an_arr_to_int(vec)

def softmax_part1_inv0_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    # First loop
    input, max_pos = reads
    i, max_val = writes
    vec = choose(input, input[:i])
    i_lower_bound = choose(Int(0), Int(1))
    i_upper_bound = choose(max_pos, input.len())

    return and_objects(
        i >= i_lower_bound,
        i <= i_upper_bound,
        max_val == an_arr_to_int(vec)
    )

def softmax_part1_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        reduce_sum,
        reduce_mul,
        reduce_max
    ]

def softmax_part2_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        vec_elemwise_add,
        vec_elemwise_mul,
        vec_scalar_mul,
        vec_scalar_add,
        reduce_sum,
        reduce_mul,
        vec_exp_map,
        exp
    ]

def softmax_part2_ps_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    ret_val = writes[0]
    input, max_pos, max_val = reads
    scalar = choose(max_val, 0 - max_val)
    vec = choose(input, input[:max_pos])
    return ret_val == an_arr_to_arr(an_int_and_arr_to_arr(scalar, vec))


def softmax_part2_inv0_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    # Second loop
    input, max_pos, max_val = reads
    out, cur, i = writes
    scalar = choose(max_val, 0 - max_val)
    vec = choose(input, input[:max_pos], input[:i])
    lower_bound = choose(Int(0), Int(1))
    upper_bound = choose(max_pos, input.len())

    return and_objects(
        i >= lower_bound,
        i <= upper_bound,
        out == an_arr_to_arr(an_int_and_arr_to_arr(scalar, vec))
    )

if __name__ == "__main__":
    # # Synthesize part 1
    # driver = Driver()
    # softmax_part1 = driver.analyze(
    #     llvm_filepath="tests/llvm/gaudi/softmax_part1.ll",
    #     loops_filepath="tests/llvm/gaudi/softmax_part1.loops",
    #     fn_name="softmax_part1",
    #     target_lang_fn=softmax_part1_target_lang,
    #     inv_grammars={
    #         "softmax_part1_inv0": InvGrammar(softmax_part1_inv0_grammar, []),
    #     },
    #     ps_grammar=softmax_part1_ps_grammar
    # )

    # input_var = mlList(Int, "input")
    # max_pos_var = Int("max_pos")
    # driver.add_var_objects([input_var, max_pos_var])
    # driver.add_precondition(input_var.len() > 0)
    # driver.add_precondition(max_pos_var <= input_var.len())
    # driver.add_precondition(max_pos_var >= 1)

    # softmax_part1(input_var, max_pos_var)
    # driver.synthesize(noVerify=True)

    # Synthesize part 2
    driver = Driver()
    softmax_part2 = driver.analyze(
        llvm_filepath="tests/llvm/gaudi/softmax_part2.ll",
        loops_filepath="tests/llvm/gaudi/softmax_part2.loops",
        fn_name="softmax_part2",
        target_lang_fn=softmax_part2_target_lang,
        inv_grammars={
            "softmax_part2_inv0": InvGrammar(softmax_part2_inv0_grammar, []),
        },
        ps_grammar=softmax_part2_ps_grammar
    )

    input_var = mlList(Int, "input")
    max_pos_var = Int("max_pos")
    max_val_var = Int("max_val")
    driver.add_var_objects([input_var, max_pos_var, max_val_var])
    driver.add_precondition(input_var.len() > 0)
    driver.add_precondition(max_pos_var <= input_var.len())
    driver.add_precondition(max_pos_var >= 1)

    softmax_part2(input_var, max_pos_var, max_val_var, uninterp_fns=[exp.name()])
    driver.synthesize(
        uninterp_fns=[exp.name()],
        unboundedInts=True,
        noVerify=True
    )

