from pathlib import Path

from tenspiler.llm.scripts.utils import run_claude

TENSPILER_LLM_PATH = Path(__file__).parent.parent.resolve()
BENCHMARKS_PATH = TENSPILER_LLM_PATH / "benchmarks"
DSL_CODE_PATH = TENSPILER_LLM_PATH / "python_dsl.py"

# Clients

with open(DSL_CODE_PATH) as f:
    dsl_code = f.read()
all_suites = {"blend", "llama", "polybench"}
for suite in all_suites:
    print("=====================")
    print(f"Running suite {suite}")
    for file in (BENCHMARKS_PATH / suite).rglob("*.cc"):
        print("--------------------------")
        print(f"Running benchmark {file.name}")
        with open(file) as f:
            source_code = f.read()

        solution, all_solutions = run_claude(dsl_code=dsl_code, source_code=source_code)
        if solution is None:
            print("Failed to find a solution that passes parser")
        else:
            print("Solution found that passes parser")
        print("All solutions leading up to this point:")
        for idx, solution in enumerate(all_solutions):
            print(idx, solution)
