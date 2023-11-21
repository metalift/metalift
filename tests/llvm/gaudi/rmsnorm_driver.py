from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, call, choose, fn_decl
from metalift.vc_util import and_objects
from tests.llvm.gaudi.gaudi_common import (an_arr2_to_arr, an_arr_to_int,
                                           an_int_and_arr_to_arr, reduce_mul,
                                           reduce_sum, vec_elemwise_add,
                                           vec_elemwise_mul, vec_scalar_add,
                                           vec_scalar_mul)
from tests.python.utils.utils import codegen

SQRT_FN_NAME = "sqrt"

def call_sqrt(x: Int) -> Int:
    return call(SQRT_FN_NAME, Int, x)

def rmsnorm_part1_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        vec_elemwise_add,
        vec_elemwise_mul,
        reduce_sum,
        reduce_mul,
    ]

def rmsnorm_part1_ps_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    ret_val = writes[0]
    input, weight = reads
    input_or_weight = choose(input, weight)
    return ret_val == an_arr_to_int(
        an_arr2_to_arr(input_or_weight, input_or_weight)
    )

def rmsnorm_part1_inv0_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    # First loop
    input, weight = reads
    i, ss = writes
    vec = choose(input, weight, input[:i], weight[:i])

    return and_objects(
        i >= 0,
        i <= input.len(),
        ss == an_arr_to_int(an_arr2_to_arr(vec, vec))
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
    rmsnorm_part1 = driver.analyze(
        llvm_filepath="tests/llvm/gaudi/rmsnorm_part1.ll",
        loops_filepath="tests/llvm/gaudi/rmsnorm_part1.loops",
        fn_name="rmsnorm_part1",
        target_lang_fn=rmsnorm_part1_target_lang,
        inv_grammars={
            "rmsnorm_part1_inv0": InvGrammar(rmsnorm_part1_inv0_grammar, []),
        },
        ps_grammar=rmsnorm_part1_ps_grammar
    )

    input_var = mlList(Int, "input")
    weight_var = mlList(Int, "weight")
    driver.add_var_objects([input_var, weight_var])
    driver.add_precondition(input_var.len() == weight_var.len())
    driver.add_precondition(input_var.len() > 0)

    rmsnorm_part1(input_var, weight_var)
    driver.synthesize()

    # Synthesize the second loop
    driver = Driver()
    rmsnorm_part2 = driver.analyze(
        llvm_filepath="tests/llvm/gaudi/rmsnorm_part2.ll",
        loops_filepath="tests/llvm/gaudi/rmsnorm_part2.loops",
        fn_name="rmsnorm_part2",
        target_lang_fn=rmsnorm_part2_target_lang,
        inv_grammars={
            "rmsnorm_part2_inv0": InvGrammar(rmsnorm_part2_inv0_grammar, ["inv_ss"]),
        },
        ps_grammar=rmsnorm_part2_ps_grammar
    )

    input_var = mlList(Int, "input")
    weight_var = mlList(Int, "weight")
    ss = Int("ss")
    driver.add_var_objects([input_var, weight_var, ss])
    driver.add_precondition(input_var.len() == weight_var.len())
    driver.add_precondition(input_var.len() > 0)

    rmsnorm_part2(input_var, weight_var, ss, uninterp_fns=[SQRT_FN_NAME])

    driver.synthesize(
        uninterp_fns=[SQRT_FN_NAME],
        unboundedInts=True
    )

    print("\n\ngenerated code:" + rmsnorm_part2.codegen(codegen))
