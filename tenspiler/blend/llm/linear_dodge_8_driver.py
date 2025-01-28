import time

from metalift.frontend.llvm import Driver
from metalift.ir import Int, Matrix
from tenspiler.constants import TENSPILER_FNS
from tenspiler.llm.scripts.models import LLMModel
from tenspiler.utils.synthesis_utils import run_llm_synthesis_algorithm

if __name__ == "__main__":
    driver = Driver()
    linear_dodge_8 = driver.analyze(
        llvm_filepath="tenspiler/blend/cpp/for_synthesis/linear_dodge_8.ll",
        loops_filepath="tenspiler/blend/cpp/for_synthesis/linear_dodge_8.loops",
        fn_name="linear_dodge_8",
        target_lang_fn=lambda: TENSPILER_FNS,
    )

    base = Matrix(Int, "base")
    active = Matrix(Int, "active")
    driver.add_var_objects([base, active])

    # Add preconditions
    driver.add_precondition(base.len() > 1)
    driver.add_precondition(base.len() == active.len())
    driver.add_precondition(base[0].len() == active[0].len())

    start_time = time.time()
    linear_dodge_8(base, active)
    run_llm_synthesis_algorithm(
        driver=driver,
        source_file="tenspiler/blend/cpp/for_synthesis/linear_dodge_8.cc",
        suite_name="blend",
        benchmark_name="linear_dodge_8",
        llm_model=LLMModel.GPT,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
