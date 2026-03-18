# Recursive call helper
import time

from llm.synthesis import LLMModel, VerificationMethod, run_synthesis_for_cc
from metalift.frontend.llvm import Driver
from metalift.ir import Int, List, Object, call, fn_decl_recursive, ite

CONV1D = "conv1d"


def call_conv_1d(input: List[Int], filter: List[Int]) -> Int:
    return call(CONV1D, Int, input, filter)


# Recursive body
def conv_1d_body(input: List[Int], filter: List[Int]) -> Int:
    vec_size = filter.len()
    cur_input = input[0]
    cur_filter = filter[0]
    input_rest = input[1:]
    filter_rest = filter[1:]
    recursed = call_conv_1d(input_rest, filter_rest)
    general_answer = cur_input * cur_filter + recursed
    return ite(vec_size < 1, Int(0), general_answer)


x = List(Int, "x")
y = List(Int, "y")
conv_1d = fn_decl_recursive(CONV1D, Int, conv_1d_body(x, y), x, y)


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
        dsl_fns=[conv_1d],
        verification_method=VerificationMethod.ROSETTE,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
