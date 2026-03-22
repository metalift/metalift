import time

from llm.synthesis import LLMModel, VerificationMethod, run_synthesis_for_cc
from metalift.frontend.llvm import Driver
from metalift.ir import Int, List, Object, call, fn_decl, fn_decl_recursive, ite
from tenspiler.axioms import (
    list_take_axiom,
    list_take_length_axiom,
    vec_elemwise_mul_axiom,
    vec_elemwise_mul_list_append_axiom,
    vec_scalar_mul_axiom,
    vec_scalar_mul_list_append_axiom,
)

# ── vec_elemwise_mul ────────────────────────────────────────────────
VEC_ELEMWISE_MUL = "vec_elemwise_mul"


def call_vec_elemwise_mul(x: List[Int], y: List[Int]) -> List[Int]:
    return call(VEC_ELEMWISE_MUL, List[Int], x, y)


def vec_elemwise_mul_body(x: List[Int], y: List[Int]) -> List[Int]:
    vec_size = x.len()
    cur = x[0] * y[0]
    recursed = call_vec_elemwise_mul(x[1:], y[1:])
    general_answer = recursed.prepend(cur)
    return ite(vec_size < 1, List.empty(Int), general_answer)


x = List(Int, "x")
y = List(Int, "y")
vec_elemwise_mul = fn_decl_recursive(
    VEC_ELEMWISE_MUL, List[Int], vec_elemwise_mul_body(x, y), x, y
)

# ── vec_scalar_mul ──────────────────────────────────────────────────
VEC_SCALAR_MUL = "vec_scalar_mul"


def call_vec_scalar_mul(a: Int, x: List[Int]) -> List[Int]:
    return call(VEC_SCALAR_MUL, List[Int], a, x)


def vec_scalar_mul_body(a: Int, x: List[Int]) -> List[Int]:
    vec_size = x.len()
    cur = a * x[0]
    recursed = call_vec_scalar_mul(a, x[1:])
    general_answer = recursed.prepend(cur)
    return ite(vec_size < 1, List.empty(Int), general_answer)


a = Int("a")
x = List(Int, "x")
vec_scalar_mul = fn_decl_recursive(
    VEC_SCALAR_MUL, List[Int], vec_scalar_mul_body(a, x), a, x
)

# ── integer_sqrt ────────────────────────────────────────────────────
INTEGER_SQRT = "integer_sqrt"


def call_integer_sqrt(x: Int) -> Int:
    return call(INTEGER_SQRT, Int, x)


integer_sqrt = fn_decl(INTEGER_SQRT, Int, Int("x"), Int("x"))


# ── preconditions ────────────────────────────────────────────────────
def _rmsnorm_part2_preconditions(driver: Driver, input_vars: dict[str, Object]) -> None:
    input_var = input_vars["input"]
    weight_var = input_vars["weight"]
    ss_var = input_vars["ss"]

    driver.add_precondition(input_var.len() >= 1)
    driver.add_precondition(input_var.len() == weight_var.len())
    driver.add_precondition(ss_var > Int(0))  # avoid division by zero


# ── main ─────────────────────────────────────────────────────────────
if __name__ == "__main__":
    start_time = time.time()
    run_synthesis_for_cc(
        cc_path="tests/tutorial/rmsnorm/rmsnorm_part2.cc",
        fn_name="rmsnorm_part2",
        precondition_fn=_rmsnorm_part2_preconditions,
        llm_model=LLMModel.BEDROCK,
        dsl_fns=[
            vec_elemwise_mul,  # op 5: col scale
            vec_scalar_mul,  # op 4: row scale
            integer_sqrt,  # op 3: reciprocal sqrt
        ],
        verification_method=VerificationMethod.SMT,
        additional_axioms=[
            list_take_axiom,
            vec_elemwise_mul_axiom,
            vec_scalar_mul_axiom,
            vec_elemwise_mul_list_append_axiom,
            vec_scalar_mul_list_append_axiom,
            list_take_length_axiom,
        ],
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
