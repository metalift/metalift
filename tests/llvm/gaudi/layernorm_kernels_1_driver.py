from collections import defaultdict
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import (Bool, FnDecl, FnDeclRecursive, Int,
                         List as mlList, Object, choose)
from metalift.vc_util import and_objects
from tests.llvm.gaudi.gaudi_common import (an_arr2_to_arr, an_arr_to_int,
                                           an_int_and_arr_to_arr,
                                           broadcast_add, elemwise_mul,
                                           reduce_mul, reduce_sum, scalar_mul,
                                           vector_add)
from tests.python.utils.utils import codegen


def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [vector_add, elemwise_mul, scalar_mul, broadcast_add, reduce_sum, reduce_mul]

def ps_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    input = reads[0]
    weight = reads[1]
    epsilon = reads[2]
    hidden_size = reads[3]
    ret_val = writes[0]

    an_arr = choose(input, weight)
    an_int = choose(epsilon, hidden_size, Int(-1), Int(0), Int(1), Int(2), Int(3))

    computed_arr = choose(
        an_arr2_to_arr(an_arr, an_arr),
        an_int_and_arr_to_arr(an_int, an_arr)
    )
    return ret_val == an_arr_to_int(computed_arr)

def inv_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    input = reads[0]
    weight = reads[1]
    epsilon = reads[2]
    hidden_size = reads[3]
    i = writes[0]
    variance = writes[1]

    an_int = choose(epsilon, hidden_size, Int(-1), Int(0), Int(1), Int(2), Int(3), i, variance)
    an_arr = choose(input, weight)
    an_arr = choose(an_arr, an_arr[:an_int])

    computed_arr = choose(an_arr2_to_arr(an_arr, an_arr), an_int_and_arr_to_arr(an_int, an_arr))

    return and_objects(
        i >= 0,
        i <= input.len(),
        an_int == an_arr_to_int(computed_arr)
    )

if __name__ == "__main__":
    driver = Driver()
    layernorm_kernels_1 = driver.analyze(
        "tests/llvm/gaudi/vllm_cuda.ll",
        "tests/llvm/gaudi/vllm_cuda.loops",
        "layernorm_kernels_1",
        target_lang,
        defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar
    )
    input_var = mlList(Int, "input")
    weight_var = mlList(Int, "weight")
    epsilon_var = Int("epsilon")
    hidden_size_var = Int("hidden_size")
    driver.add_var_objects([input_var, weight_var, epsilon_var, hidden_size_var])
    driver.add_precondition(input_var.len() == weight_var.len())
    driver.add_precondition(input_var.len() > 0)

    layernorm_kernels_1(input_var, weight_var, epsilon_var, hidden_size_var)
    driver.synthesize(noVerify=True)

    print("\n\ngenerated code:" + layernorm_kernels_1.codegen(codegen))