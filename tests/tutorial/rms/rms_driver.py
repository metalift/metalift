import time

from llm.synthesis import LLMModel, VerificationMethod, run_synthesis_for_cc
from metalift.frontend.llvm import Driver
from metalift.ir import Object
from tenspiler.tenspiler_common import (
    integer_sqrt,
    reduce_sum,
    vec_elemwise_mul,
    vec_map,
    vec_scalar_mul,
)


def _rmsnorm_preconditions(driver: Driver, input_vars: dict[str, Object]) -> None:
    input_var = input_vars["input"]
    weight_var = input_vars["weight"]

    driver.add_precondition(input_var.len() >= 1)
    driver.add_precondition(input_var.len() == weight_var.len())


# ── main ─────────────────────────────────────────────────────────────
if __name__ == "__main__":
    start_time = time.time()
    run_synthesis_for_cc(
        cc_path="tests/tutorial/rms/rms.cc",
        fn_name="rmsnorm",
        precondition_fn=_rmsnorm_preconditions,
        llm_model=LLMModel.GPT,
        dsl_fns=[
            vec_elemwise_mul,
            vec_scalar_mul,
            reduce_sum,
            integer_sqrt,
            vec_map,
        ],
        verification_method=VerificationMethod.SMT,
        list_bound=2,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
