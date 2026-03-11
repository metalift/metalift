"""
Driver for LLM-guided synthesis of softmax_part1 and similar single-loop .cc functions.
"""
import time

from llm.synthesis import VerificationMethod, run_synthesis_for_cc
from metalift.frontend.llvm import Driver
from metalift.ir import Object


def _softmax_part1_preconditions(driver: Driver, input_vars: dict[str, Object]) -> None:
    """Add preconditions for softmax_part1: non-empty input, max_pos in range."""
    input_var = input_vars["input"]
    max_pos_var = input_vars["max_pos"]
    driver.add_precondition(input_var.len() > 0)
    driver.add_precondition(max_pos_var <= input_var.len())
    driver.add_precondition(max_pos_var >= 1)


if __name__ == "__main__":
    start_time = time.time()
    run_synthesis_for_cc(
        "tenspiler/llama/cpp/for_synthesis/softmax/softmax_part1.cc",
        "softmax_part1",
        precondition_fn=_softmax_part1_preconditions,
        verification_method=VerificationMethod.SMT,
    )
    print(f"Synthesis took {time.time() - start_time} seconds")
