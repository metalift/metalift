from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int, ite
from metalift.ir import List as mlList
from metalift.ir import Object, call, choose, fn_decl
from metalift.vc_util import and_objects
from tests.llvm.gaudi.gaudi_common import (an_arr2_to_arr, an_arr_to_int,
                                           an_int_and_arr_to_arr, call_reduce_max, reduce_mul,
                                           reduce_sum, vec_elemwise_add,
                                           vec_elemwise_mul, vec_scalar_add,
                                           vec_scalar_mul, reduce_max)
from tests.python.utils.utils import codegen

SQRT_FN_NAME = "sqrt"

def call_sqrt(x: Int) -> Int:
    return call(SQRT_FN_NAME, Int, x)

def softmax_part1_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        reduce_sum,
        reduce_mul,
        reduce_max
    ]

def softmax_part1_ps_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    ret_val = writes[0]
    input, max_pos = reads
    return ret_val == call_reduce_max(input)

def softmax_part1_inv0_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    # First loop
    input, max_pos = reads
    i, max_val = writes
    vec = choose(input, input[:i])

    return and_objects(
        i >= 0,
        i <= input.len(),
        max_val == call_reduce_max(input[:i])
    )

def rmsnorm_part2_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    x = Int("x")
    sqrt = fn_decl(SQRT_FN_NAME, Int, None, x)
    return [
        vec_elemwise_add,
        vec_elemwise_mul,
        vec_scalar_mul,
        vec_scalar_add,
        reduce_sum,
        reduce_mul,
        sqrt
    ]

def rmsnorm_part2_ps_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    ret_val = writes[0]
    input, weight, ss = reads
    input_or_weight = choose(input, weight)
    inv_ss = 1 // call_sqrt(ss // input.len() + 1)
    return ret_val == an_int_and_arr_to_arr(
        inv_ss,
        an_arr2_to_arr(input_or_weight, input_or_weight)
    )


def rmsnorm_part2_inv0_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    # Second loop
    input, weight, ss = reads
    out = writes[0]
    i = writes[1]
    inv_ss = 1 // call_sqrt(ss // input.len() + 1)
    vec = choose(input, weight, input[:i], weight[:i])
    return and_objects(
        i >= 0,
        i <= input.len(),
        out == an_int_and_arr_to_arr(inv_ss, an_arr2_to_arr(vec, vec))
    )

if __name__ == "__main__":
    # Synthesize the first loop
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

    softmax_part1(input_var, max_pos_var)
    driver.synthesize(noVerify=True)

