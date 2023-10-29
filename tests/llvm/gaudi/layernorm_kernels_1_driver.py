from collections import defaultdict
from typing import List

from metalift.frontend.llvm import Driver
from metalift.ir import BoolObject, IntObject, ListObject, NewObject, choose, implies
from metalift.vc_util import and_objects
from tests.python.utils.utils import codegen
from tests.llvm.gaudi.gaudi_common import an_arr2_to_arr, an_int_and_arr_to_arr, an_arr_to_int, target_lang

def ps_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> BoolObject:
    input = reads[0]
    weight = reads[1]
    epsilon = reads[2]
    hidden_size = reads[3]
    ret_val = writes[0]

    an_arr = choose(input, weight)
    an_int = choose(epsilon, hidden_size, IntObject(-1), IntObject(0), IntObject(1), IntObject(2), IntObject(3))

    computed_arr = choose(
        an_arr2_to_arr(an_arr, an_arr),
        an_int_and_arr_to_arr(an_int, an_arr)
    )
    return ret_val == an_arr_to_int(computed_arr)

def inv_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> BoolObject:
    input = reads[0]
    weight = reads[1]
    epsilon = reads[2]
    hidden_size = reads[3]
    variance = writes[0]
    i = writes[1]

    an_int = choose(epsilon, hidden_size, IntObject(-1), IntObject(0), IntObject(1), IntObject(2), IntObject(3), i, variance)
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
        defaultdict(lambda: inv_grammar),
        ps_grammar
    )
    input_var = ListObject(IntObject, "input")
    weight_var = ListObject(IntObject, "weight")
    epsilon_var = IntObject("epsilon")
    hidden_size_var = IntObject("hidden_size")
    driver.add_var_objects([input_var, weight_var, epsilon_var, hidden_size_var])
    driver.add_precondition(input_var.len() == weight_var.len())
    driver.add_precondition(input_var.len() > 0)

    layernorm_kernels_1(input_var, weight_var, epsilon_var, hidden_size_var)
    driver.synthesize(noVerify=True)

    print("\n\ngenerated code:" + layernorm_kernels_1.codegen(codegen))