import time

from llm.synthesis import LLMModel, VerificationMethod, run_synthesis_for_cc
from metalift.frontend.llvm import Driver
from metalift.ir import Int, List, Object, call, fn_decl_recursive, ite
from tenspiler.axioms import reduce_sum_vec_elemwise_mul_axiom

# ── reduce_sum ──────────────────────────────────────────────────────
REDUCE_SUM = "reduce_sum"


def call_reduce_sum(x: List[Int]) -> Int:
    return call(REDUCE_SUM, Int, x)


def reduce_sum_body(x: List[Int]) -> Int:
    vec_size = x.len()
    cur = x[0]
    recursed = call_reduce_sum(x[1:])
    general_answer = cur + recursed
    return ite(vec_size < 1, Int(0), general_answer)


x = List(Int, "x")
reduce_sum = fn_decl_recursive(REDUCE_SUM, Int, reduce_sum_body(x), x)

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


# ── preconditions ────────────────────────────────────────────────────
def _rmsnorm_part1_preconditions(driver: Driver, input_vars: dict[str, Object]) -> None:
    input_var = input_vars["input"]
    driver.add_precondition(input_var.len() >= 1)


# ── main ─────────────────────────────────────────────────────────────
if __name__ == "__main__":
    start_time = time.time()
    run_synthesis_for_cc(
        cc_path="tests/tutorial/rmsnorm_part1/rmsnorm_part1.cc",
        fn_name="rmsnorm_part1",
        precondition_fn=_rmsnorm_part1_preconditions,
        llm_model=LLMModel.BEDROCK,
        dsl_fns=[
            reduce_sum,  # op 2: sum of squares
            vec_elemwise_mul,  # op 1: element-wise square
        ],
        verification_method=VerificationMethod.SMT,
        additional_axioms=[reduce_sum_vec_elemwise_mul_axiom],
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
