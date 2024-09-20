import json
import os
import time
from pathlib import Path
from textwrap import dedent
from typing import Any

import anthropic

from tenspiler.llm.parser import check_solution, remove_comments
from tenspiler.llm.scripts.utils import TEMPLATE_SYS, get_fuzzer_feedback, get_ps_text


def _found_correct_parser_solution(info: dict[str, Any]) -> bool:
    return len(info["parser_solutions"]) > 0 and info["parser_solutions"][-1][1] is None


def _found_correct_fuzzer_solution(info: dict[str, Any]) -> bool:
    return len(info["fuzzer_solutions"]) > 0 and info["fuzzer_solutions"][-1][1] is None


def _run_test(func_name: str, ps_sol: str, inputs: dict[str, Any]) -> int:
    universal_imports = f"""
    from tenspiler.llm.python_dsl import *
    from typing import Any, Callable, List
    """
    ps_sol = dedent(remove_comments(dedent(universal_imports) + dedent(ps_sol)))
    namespace = {}
    exec(ps_sol, namespace)
    return namespace[func_name](**inputs)


# Define all the clients that are needed
claude_client = anthropic.Anthropic(api_key=os.getenv("CLAUDE_API_KEY"))


def run_claude(
    *,
    benchmark_name: str,
    dsl_code: str,
    source_code: str,
    test_case_dir: Path,
    max_parser_tries: int = 5,
    max_fuzzer_tries: int = 5,
) -> dict[str, Any]:
    """
    The flow of the function is as follows:
    1. Start with asking the model to rewrite the function.
    2. Check if solution passes the parser. If it does, proceed. Otherwise, give parser feedback and ask the model to fix the function. Repeat this step for `max_parser_tries` times.
    3. If the solution passes the parser, ask the model to run all test cases in the directory `test_case_dir`. If all test cases pass, return the solution. Otherwise, give feedback on the failed fuzzer input-output pair and ask the model to fix the function. Repeat this step for `max_fuzzer_tries` times.
    4. If the solution passes all test cases, return the solution. Otherwise, return None.


    we return a dictionary with the following keys:
    - parser_solutions: A list of solutions that we tried to pass to parser. Each solution is in the form of (solution, feedback, time_taken) tuple. For the correct solution, feedback is None.
    - fuzzer_solutions: A list of solutions that we tried to pass to fuzzer. Each solution is in the form of (solution, feedback, time_taken) tuple. For the correct solution, feedback is None.
    - num_parser_tries: Number of times we tried to pass a solution to the parser.
    - num_fuzzer_tries: Number of times we tried to pass a solution to the fuzzer.
    """
    info: dict[str, Any] = {
        "parser_solutions": [],
        "fuzzer_solutions": [],
        "num_parser_tries": 0,
        "num_fuzzer_tries": 0,
    }
    ps_text = get_ps_text(dsl_code, source_code)
    # We start with a single message, will append with feedback
    messages = [
        {"role": "user", "content": ps_text},
    ]
    for _ in range(max_parser_tries):
        parser_try_start_time = time.time()
        message = claude_client.messages.create(
            model="claude-3-5-sonnet-20240620",
            max_tokens=1000,
            temperature=0.0,
            system=TEMPLATE_SYS,
            messages=messages,
        )
        curr_solution = message.content[0].text
        print("Solution is", curr_solution)
        curr_parser_feedback = None
        try:
            check_solution(curr_solution, 1)
            print("Solution passed the parser")
            break
        except Exception as e:
            print("Failed to pass the parser", e)
            curr_parser_feedback = str(e)
            messages.extend(
                [
                    {"role": "assistant", "content": curr_solution},
                    {"role": "user", "content": curr_parser_feedback},
                ]
            )
        finally:
            parser_try_end_time = time.time()
            parser_try_time_taken = parser_try_end_time - parser_try_start_time
            info["parser_solutions"].append(
                (solution, curr_parser_feedback, parser_try_time_taken)
            )

    if not _found_correct_parser_solution(info):
        # For now, we just claim it failed and returned. In the future, we might want to go back to the beginning and ask the model to rewrite the function.
        return info

    print("===================")
    print("Moving on to fuzzer")
    for _ in range(max_fuzzer_tries):
        curr_fuzzer_feedback = None
        fuzzer_try_start_time = time.time()
        for test_case_file in test_case_dir.rglob("*.json"):
            with open(test_case_file) as f:
                test_data = json.load(f)
                expected = test_data["result"]
                del test_data["result"]
                # run the function here
                actual = _run_test(
                    func_name=benchmark_name, ps_sol=curr_solution, inputs=test_data
                )
                if actual != expected:
                    curr_fuzzer_feedback = get_fuzzer_feedback(
                        inputs=test_data,
                        expected_output=expected,
                        actual_output=actual,
                    )
                    messages.extend(
                        [
                            {"role": "assistant", "content": solution},
                            {"role": "user", "content": curr_fuzzer_feedback},
                        ]
                    )
                    break

        fuzzer_try_end_time = time.time()
        fuzzer_try_time_taken = fuzzer_try_end_time - fuzzer_try_start_time
        info["fuzzer_solutions"].append(
            (solution, curr_fuzzer_feedback, fuzzer_try_time_taken)
        )

        if _found_correct_fuzzer_solution(info):
            return info

    return info


TENSPILER_LLM_PATH = Path(__file__).parent.parent.resolve()
BENCHMARKS_PATH = TENSPILER_LLM_PATH / "benchmarks"
DSL_CODE_PATH = TENSPILER_LLM_PATH / "python_dsl.py"

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
