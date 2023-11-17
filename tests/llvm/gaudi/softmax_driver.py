from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tests.llvm.gaudi.gaudi_common import (an_arr_to_arr, an_arr_to_int,
                                           an_int_and_arr_to_arr, exp,
                                           reduce_max, reduce_mul, reduce_sum,
                                           vec_exp_map, vec_scalar_add,
                                           vec_scalar_div, vec_scalar_mul)


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
        vec_scalar_mul,
        vec_scalar_add,
        vec_scalar_div,
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

def softmax_part3_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [reduce_sum, reduce_mul, reduce_max]

def softmax_part3_ps_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    ret_val = writes[0]
    output, max_pos = reads
    return ret_val == an_arr_to_int(choose(output, output[:max_pos]))


def softmax_part3_inv0_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    output, max_pos = reads
    i, sum = writes
    lower_bound = choose(Int(0), Int(1))
    upper_bound = choose(max_pos, output.len())

    return and_objects(
        i >= lower_bound,
        i <= upper_bound,
        sum == an_arr_to_int(choose(output, output[:max_pos], output[:i]))
    )

def softmax_part4_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [vec_scalar_add, vec_scalar_mul, vec_scalar_div]

def softmax_part4_ps_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    ret_val = writes[0]
    unnormalized_output, max_pos, sum = reads
    vec = choose(unnormalized_output, unnormalized_output[:max_pos])
    return ret_val == an_int_and_arr_to_arr(sum, vec)


def softmax_part4_inv0_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    unnormalized_output, max_pos, sum = reads
    out, i, _ = writes
    lower_bound = choose(Int(0), Int(1))
    upper_bound = choose(max_pos, unnormalized_output.len())
    vec = choose(unnormalized_output, unnormalized_output[:max_pos], unnormalized_output[:i])

    return and_objects(
        i >= lower_bound,
        i <= upper_bound,
        out == an_int_and_arr_to_arr(sum, vec)
    )

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

    # Synthesize part 3
    driver = Driver()
    softmax_part3 = driver.analyze(
        llvm_filepath="tests/llvm/gaudi/softmax_part3.ll",
        loops_filepath="tests/llvm/gaudi/softmax_part3.loops",
        fn_name="softmax_part3",
        target_lang_fn=softmax_part3_target_lang,
        inv_grammars={
            "softmax_part3_inv0": InvGrammar(softmax_part3_inv0_grammar, []),
        },
        ps_grammar=softmax_part3_ps_grammar
    )

    output_var = mlList(Int, "output")
    max_pos_var = Int("max_pos")
    driver.add_var_objects([output_var, max_pos_var])
    driver.add_precondition(output_var.len() > 0)
    driver.add_precondition(max_pos_var <= output_var.len())
    driver.add_precondition(max_pos_var >= 1)

    softmax_part3(output_var, max_pos_var)
    driver.synthesize(noVerify=True)

    # Synthesize part 4
    driver = Driver()
    softmax_part4 = driver.analyze(
        llvm_filepath="tests/llvm/gaudi/softmax_part4.ll",
        loops_filepath="tests/llvm/gaudi/softmax_part4.loops",
        fn_name="softmax_part4",
        target_lang_fn=softmax_part4_target_lang,
        inv_grammars={
            "softmax_part4_inv0": InvGrammar(softmax_part4_inv0_grammar, []),
        },
        ps_grammar=softmax_part4_ps_grammar
    )

    unnormalized_output_var = mlList(Int, "unnormalized_output")
    max_pos_var = Int("max_pos")
    sum_var = Int("sum")
    driver.add_var_objects([unnormalized_output_var, max_pos_var, sum_var])
    driver.add_precondition(unnormalized_output_var.len() > 0)
    driver.add_precondition(max_pos_var <= unnormalized_output_var.len())
    driver.add_precondition(max_pos_var >= 1)

    softmax_part4(unnormalized_output_var, max_pos_var, sum_var)
    driver.synthesize(noVerify=True)