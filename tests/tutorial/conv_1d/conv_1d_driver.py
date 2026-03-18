# Recursive call helper
import time

from llm.synthesis import LLMModel, VerificationMethod, run_synthesis_for_cc
from metalift.frontend.llvm import Driver
from metalift.ir import Int, List, Object, call, fn_decl_recursive, ite
from tenspiler.tenspiler_common import (
    call_reduce_sum,
    call_vec_elemwise_mul,
    reduce_sum,
    vec_elemwise_mul,
)

CONV1D = "conv1d"


def call_conv_1d(input: List[Int], filter: List[Int], W: Int, W_f: Int) -> List[Int]:
    return call(CONV1D, List[Int], input, filter, W, W_f)


# Recursive body
def conv_1d_body(input: List[Int], filter: List[Int], W: Int, W_f: Int) -> Int:
    element = call_reduce_sum(call_vec_elemwise_mul(input[:W_f], filter))
    recursed = call_conv_1d(input[1:], filter, W - 1, W_f)
    general_answer = recursed.prepend(element)
    return ite(W < 1, List.empty(Int), general_answer)


x = List(Int, "x")
y = List(Int, "y")
W = Int("W")
W_f = Int("W_f")
conv_1d = fn_decl_recursive(CONV1D, Int, conv_1d_body(x, y, W, W_f), x, y, W, W_f)


def _conv_1d_preconditions(driver: Driver, input_vars: dict[str, Object]) -> None:
    input_var = input_vars["input"]
    filter_var = input_vars["filter"]
    W = input_vars["W"]
    W_f = input_vars["W_f"]
    driver.add_precondition(W >= 1)
    driver.add_precondition(W_f >= 1)
    driver.add_precondition(input_var.len() >= W + W_f)
    driver.add_precondition(filter_var.len() >= 1)


if __name__ == "__main__":
    start_time = time.time()
    run_synthesis_for_cc(
        cc_path="tests/tutorial/conv_1d/conv_1d.cc",
        fn_name="conv_1d",
        precondition_fn=_conv_1d_preconditions,
        llm_model=LLMModel.GPT,
        dsl_fns=[conv_1d, vec_elemwise_mul, reduce_sum],
        verification_method=VerificationMethod.ROSETTE,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
