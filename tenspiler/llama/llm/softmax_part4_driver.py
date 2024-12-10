import time

from metalift.frontend.llvm import Driver
from tenspiler.llm.scripts.models import LLMModel
from tenspiler.llm.scripts.utils import analyze_benchmark
from tenspiler.utils.synthesis_utils import run_llm_synthesis_algorithm

if __name__ == "__main__":
    start_time = time.time()
    driver = Driver()
    input_code = analyze_benchmark(driver, "softmax_part4")
    run_llm_synthesis_algorithm(
        driver=driver,
        source_code=input_code,
        suite_name="llama",
        benchmark_name="softmax_part4",
        llm_model=LLMModel.GPT,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
