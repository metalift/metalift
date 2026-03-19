# Recursive call helper
import time

from llm.synthesis import LLMModel, VerificationMethod, run_synthesis_for_cc
from metalift.frontend.llvm import Driver
from metalift.ir import Int, List, Matrix, Object, Or, call, fn_decl_recursive, ite

# Dot product
DOT = "dot"


def call_dot(x: List[Int], f: List[Int]) -> Int:
    return call(DOT, Int, x, f)


def dot_body(x: List[Int], f: List[Int]) -> Int:
    vec_size = f.len()
    cur = x[0] * f[0]
    recursed = call_dot(x[1:], f[1:])
    general_answer = cur + recursed
    return ite(vec_size < 1, Int(0), general_answer)


x = List(Int, "x")
f = List(Int, "f")
dot = fn_decl_recursive(DOT, Int, dot_body(x, f), x, f)

CONV_1D = "conv_1d"


def call_conv_1d(x: List[Int], f: List[Int]) -> List[Int]:
    return call(CONV_1D, List[Int], x, f)


def conv_1d_body(x: List[Int], f: List[Int]) -> List[Int]:
    x_size = x.len()
    f_size = f.len()
    cur = call_dot(x[:f_size], f)
    recursed = call_conv_1d(x[1:], f)
    general_answer = recursed.prepend(cur)
    return ite(Or(f_size < 1, x_size < f_size), List.empty(Int), general_answer)


conv_1d = fn_decl_recursive(CONV_1D, List[Int], conv_1d_body(x, f), x, f)

DEPTHWISE_CONV_1D = "depthwise_conv_1d"


def call_depthwise_conv_1d(
    inp: List[List[Int]], filters: List[List[Int]]
) -> List[List[Int]]:
    return call(DEPTHWISE_CONV_1D, List[List[Int]], inp, filters)


def depthwise_conv_1d_body(
    inp: List[List[Int]], filters: List[List[Int]]
) -> List[List[Int]]:
    vec_size = inp.len()
    cur = call_conv_1d(inp[0], filters[0])  # conv_1d of one channel
    recursed = call_depthwise_conv_1d(inp[1:], filters[1:])  # remaining channels
    general_answer = recursed.prepend(cur)
    return ite(vec_size < 1, List.empty(List[Int]), general_answer)


matrix_x = Matrix(Int, "matrix_x")
matrix_y = Matrix(Int, "matrix_y")
depthwise_conv_1d = fn_decl_recursive(
    DEPTHWISE_CONV_1D,
    List[List[Int]],
    depthwise_conv_1d_body(matrix_x, matrix_y),
    matrix_x,
    matrix_y,
)


def _conv_1d_preconditions(driver: Driver, input_vars: dict[str, Object]) -> None:
    input_var = input_vars["input"]
    filter_var = input_vars["filter"]

    driver.add_precondition(input_var.len() >= 1)
    driver.add_precondition(input_var.len() == filter_var.len())
    driver.add_precondition(filter_var[0].len() == 3)
    driver.add_precondition(input_var[0].len() >= 3)


if __name__ == "__main__":
    start_time = time.time()
    run_synthesis_for_cc(
        cc_path="tests/tutorial/conv_1d/conv_1d_smt.cc",
        fn_name="conv_1d_smt",
        precondition_fn=_conv_1d_preconditions,
        llm_model=LLMModel.GPT,
        dsl_fns=[depthwise_conv_1d, conv_1d, dot],
        verification_method=VerificationMethod.SMT,
        list_bound=3,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
