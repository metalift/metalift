import time

from metalift.frontend.llvm import Driver
from tenspiler.llm.scripts.models import LLMModel
from tenspiler.llm.scripts.utils import analyze_benchmark
from tenspiler.utils.synthesis_utils import (
    VerificationMethod,
    run_llm_synthesis_algorithm,
)

if __name__ == "__main__":
    start_time = time.time()
    driver = Driver()
    input_code = analyze_benchmark(driver, "lighten_blend_8")
    run_llm_synthesis_algorithm(
        driver=driver,
        source_code=input_code,
        suite_name="blend",
        benchmark_name="lighten_blend_8",
        llm_model=LLMModel.GPT,
        verification_method=VerificationMethod.SMT,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
