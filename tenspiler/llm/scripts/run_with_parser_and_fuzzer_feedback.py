import argparse
import copy
import json
import os
import re
from enum import Enum
from pathlib import Path
from textwrap import dedent
from typing import Any, Optional

import anthropic
import google.generativeai as genai
from openai import OpenAI

from tenspiler.llm.parser import check_solution, remove_comments
from tenspiler.llm.scripts.utils import (
    TEMPLATE_ENCLOSE_CODE,
    TEMPLATE_ERR,
    TEMPLATE_SYS,
    extract,
    get_fuzzer_feedback,
)


class LLMModel(Enum):
    CLAUDE = "claude"
    GPT = "gpt"
    GEMINI = "gemini"


def _run_fuzzer_tests_and_get_messages(
    func_name: str, ps_sol: str, test_case_dir: Path, limit: Optional[int] = None
) -> str:
    print("Running fuzzer tests")
    # Now we pass the solution to the fuzzer
    wrong_test_cases: list[str] = []
    curr_fuzzer_feedback = None
    # input = {
    #     "base": [[7, 8, 9], [10, 11, 12]],
    #     "active": [[1, 2, 3], [4, 5, 6]],
    # }
    # expected_output = [[7, 20, 25], [27, 28, 29]]
    # actual, error = _run_test(func_name=func_name, ps_sol=ps_sol, inputs=input)
    # if actual != expected_output or error is not None:
    #     curr_fuzzer_feedback = get_fuzzer_feedback(
    #         inputs=[input],
    #         expected_outputs=[expected_output],
    #         actual_or_errors=[actual or error],
    #     )
    #     return curr_fuzzer_feedback
    # return None

    for test_case_file in test_case_dir.rglob("*.json"):
        with open(test_case_file) as f:
            try:
                test_data = json.load(f)
            except:
                print("Skipping file", test_case_file)
                continue
            expected = test_data["result"]
            del test_data["result"]
            # run the function here
            assert func_name is not None
            actual, error = _run_test(
                func_name=func_name, ps_sol=ps_sol, inputs=test_data
            )
            if actual != expected or error is not None:
                wrong_test_cases.append((test_data, expected, actual, error))
                if limit is not None and len(wrong_test_cases) == limit:
                    break
    if len(wrong_test_cases) > 0:
        print("Found failed test cases")
        inputs = [test_case[0] for test_case in wrong_test_cases]
        expected_outputs = [test_case[1] for test_case in wrong_test_cases]
        actual_or_errors = [
            test_case[2] or test_case[3] for test_case in wrong_test_cases
        ]
        curr_fuzzer_feedback = get_fuzzer_feedback(
            inputs=inputs,
            expected_outputs=expected_outputs,
            actual_or_errors=actual_or_errors,
        )
        return curr_fuzzer_feedback
    return None


# Define the replacement function
def replace_ite(ps_sol: str) -> str:
    def repl_func(match):
        cond = match.group(1).strip()
        a = match.group(2).strip()
        b = match.group(3).strip()
        return f"{a} if {cond} else {b}"

    ite_pattern = r"ite\(([^,]+),\s*([^,]+),\s*([^)]+)\)"
    return re.sub(ite_pattern, repl_func, ps_sol)


def _run_test(func_name: str, ps_sol: str, inputs: dict[str, Any]) -> tuple[Any, str]:
    universal_imports = f"""
    from tenspiler.llm.python_dsl import *
    from typing import Any, Callable, List
    """
    ps_sol = dedent(remove_comments(dedent(universal_imports) + dedent(ps_sol)))
    namespace = {}
    try:
        exec(ps_sol, namespace)
        return namespace[func_name](**inputs), None
    except Exception as e:
        return None, str(e)


def get_solution_from_llm(llm_model: LLMModel, messages: list[dict[str, Any]]) -> str:
    if llm_model == LLMModel.CLAUDE:
        return get_solution_from_claude(messages)
    elif llm_model == LLMModel.GPT:
        return get_solution_from_gpt(messages)
    elif llm_model == LLMModel.GEMINI:
        return get_solution_from_gemini(messages)
    raise ValueError(f"Invalid LLM model {llm_model}")


def get_solution_from_gemini(messages: list[dict[str, Any]]) -> str:
    print("running with gemini")
    genai.configure(api_key="AIzaSyBbELW0-tYAuIHPf7DQiJ3Csik_LCbsy9c")

    generation_config = {
        "temperature": 0.7,
        "top_p": 0.95,
        "top_k": 64,
        "max_output_tokens": 8192,
        "response_mime_type": "text/plain",
    }

    model = genai.GenerativeModel(
        model_name="gemini-1.5-pro-exp-0827",  # "gemini-1.5-pro-exp-0827",
        generation_config=generation_config,
        # safety_settings = Adjust safety settings
        # See https://ai.google.dev/gemini-api/docs/safety-settings
    )

    messages_copy = copy.deepcopy(messages)
    for message in messages_copy:
        if message["role"] == "assistant":
            message["role"] = "model"
        message["parts"] = message["content"]
        del message["content"]

    chat_session = model.start_chat(history=messages_copy[:-1])
    response = chat_session.send_message(messages_copy[-1]["parts"])
    return extract(response.text)[0]


def get_solution_from_claude(messages: list[dict[str, Any]]) -> str:
    print("running with claude")
    message = claude_client.messages.create(
        model="claude-3-5-sonnet-20240620",
        max_tokens=1000,
        temperature=0.7,
        system=TEMPLATE_SYS,
        messages=messages,
    )
    raw_solution = extract(message.content[0].text)[0]
    return replace_ite(raw_solution)


def get_solution_from_gpt(messages: list[dict[str, Any]]) -> str:
    print("running with gpt")
    # messages don't include the system message
    messages_with_sys = [{"role": "system", "content": TEMPLATE_SYS}, *messages]
    outputs = openai_client.chat.completions.create(
        model="gpt-4o-2024-08-06",  # model to use
        messages=messages_with_sys,
        n=1,
        temperature=0.7,
    )
    outputs = [choice.message.content for choice in outputs.choices]
    return replace_ite(extract(outputs[0])[0])


# Define all the clients that are needed
openai_client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))
claude_client = anthropic.Anthropic(api_key=os.getenv("CLAUDE_API_KEY"))


def run_llm(
    *,
    llm_model: LLMModel,
    benchmark_name: str,
    dsl_code: str,
    source_code: str,
    test_case_dir: Path,
    max_num_tries_per_solution: int = 5,
    max_num_tries: int = 5,
) -> dict[str, Any]:
    """
    The flow of the function is as follows:
    1. Start with asking the model to rewrite the function.
    2. Check if solution passes the parser. If it does, proceed. Otherwise, give parser feedback and ask the model to fix the function. Repeat this step for `max_parser_tries` times.
    3. If the solution passes the parser, ask the model to run all test cases in the directory `test_case_dir`. If all test cases pass, return the solution. Otherwise, give feedback on the failed fuzzer input-output pair and ask the model to fix the function. Repeat this step for `max_fuzzer_tries` times.
    4. If the solution passes all test cases, return the solution. Otherwise, return None.

    we return a list with maximum length of `max_num_tries` and each element containing the following information:
    - solutions: A list of solutions that we tried to pass to parser and fuzzer. Each solution is in the form of (solution, feedback, time_taken) tuple. For the correct solution, feedback is None.
    """
    info: list[Any] = []
    ps_text = f"""
    Your task is to rewrite the given `test` C++ Function. You need to use only the set of provided functions and constants to achieve this. The rewritten program should be semantically equivalent to the `test` function. Please generate the shortest possible solution.

    #Instructions
    # 1. Do not use for/while loops for rewriting the function.
    # 2. The rewritten program should just be a single return statement of the form return provided_function(...)
    # 3. Inline all the expressions. Do not use intermediate variables. Return the function signature as well as the function body in python.

    #defined functions
    ```python
    {dsl_code}
    ```

    ```cpp
    //test function
    {source_code}
    ```
    """
    # We start with a single message, will append with feedback
    sol = f"""
    def color_burn_8(base: List[List[int]], active: List[List[int]]) -> List[List[int]]:
        return matrix_where(
            active,
            matrix_scalar_sub(32, matrix_elemwise_div(matrix_scalar_sub(32, base), active)),
            lambda a, b: 32 if a == 0 else b
        )
    """
    sol2 = f"""
    def color_burn_8(base: List[List[int]], active: List[List[int]]) -> List[List[int]]:
        return matrix_where(
            active,
            matrix_scalar_sub(32, scalar_matrix_div(32, matrix_scalar_sub(32, base))),
            lambda a, b: 32 if a == 0 else b
        )
    """
    sol3 = f"""
    def color_burn_8(base: List[List[int]], active: List[List[int]]) -> List[List[int]]:
        return matrix_where(
            active,
            matrix_scalar_sub(
                32, matrix_elemwise_div(scalar_matrix_sub(32, base), active)
            ),
            lambda a, b: 32 if a == 0 else b,
        )
    """
    manual_test_feedback = f"""
    The translated program does not match the source program on the following inputs.

    Test case 1:
    Inputs:
    - base: [[1, 2], [3, 4]]
    - active: [[1, 2], [3, 4]]
    Expected output: [[1, 17], [23, 25]]
    Generated output: [[-63, -47], [-42, -39]]
    """
    manual_test_feedback2 = f"""
    The translated program does not match the source program on the following inputs.

    Test case 1:
    Inputs:
    - base: [[1, 2], [3, 4]]
    - active: [[1, 2], [3, 4]]
    Expected output: [[1, 17], [23, 25]]
    Generated output: [[-34, -34], [-34, -34]]
    """
    manual_test_feedback3 = f"""
    The translated program does not match the source program on the following inputs.

    Test case 1:
    Inputs:
    - base: [[1, 2], [3, 4]]
    - active: [[1, 2], [3, 4]]
    Expected output: [[1, 17], [23, 25]]
    Generated output: [[-1, -17], [-23, -25]]
    """

    # ps_text += "\n" + f"""
    # <Generated solution>:
    # {sol}

    # <Feedback>:
    # {manual_test_feedback}

    # <Generated solution>:
    # {sol3}

    # <Feedback>:
    # {manual_test_feedback3}

    # Please fix the program to pass the test cases. Don't generate the same solution as before. Explain your fix.
    # """
    messages = [
        {"role": "user", "content": ps_text},
        # {"role": "assistant", "content": sol},
        # {"role": "user", "content": manual_test_feedback},
        # {"role": "assistant", "content": sol3},
        # {"role": "user", "content": manual_test_feedback3},
    ]
    for i in range(50):
        # sleep(10)
        curr_solution = get_solution_from_llm(llm_model, messages)
        # check
        print(f"===== Starting iteration {i} =====")
        print(curr_solution)
        try:
            print("Passing solution to the parser")
            func_names, _, _ = check_solution(curr_solution, 1)
            func_name = func_names[0]
            print("Passed the parser")
        except Exception as e:
            print("Failed to pass the parser", e)
            continue

        # fuzzer
        # fuzzer_feedback = _run_fuzzer_tests_and_get_messages(func_name=func_name, ps_sol=curr_solution, test_case_dir=test_case_dir)
        # if fuzzer_feedback is None:
        #     print("Correct")
        # else:
        #     print("Incorrect")
    exit(0)

    parser_feedback = f"""
    The generated solution is incorrect because matrix_scalar_sub expects a list of lists of integers as the first argument, but got an integer instead.
    """
    # messages_for_parser = [
    #     *messages,
    #     {"role": "assistant", "content": curr_solution},
    #     {"role": "user", "content": parser_feedback},
    # ]

    # passed_parser = False
    # passed_fuzzer = False
    # while not passed_fuzzer:
    #     while not passed_parser:
    #         try:
    #             print("Passing solution to the parser")
    #             func_names, _, _ = check_solution(curr_solution, 1)
    #             func_name = func_names[0]
    #             print("Parser solution passed the parser")
    #             passed_parser = True
    #         except Exception as e:
    #             print("Failed to pass the parser", e)
    #             curr_parser_feedback = str(e)
    #             messages_for_parser = [
    #                 *messages,
    #                 {"role": "assistant", "content": curr_solution},
    #                 {
    #                     "role": "user",
    #                     "content": curr_parser_feedback
    #                     + f"\n{TEMPLATE_ENCLOSE_CODE}",
    #                 },
    #             ]
    #             print("Trying to fix the solution to pass parser")
    #             curr_solution = get_solution_from_llm(
    #                 llm_model, messages_for_parser
    #             )
    #             print("New solution is", curr_solution)
    #     fuzzer_feedback = _run_fuzzer_tests_and_get_messages(func_name=func_name, ps_sol=curr_solution, test_case_dir=test_case_dir)
    #     print("Fuzzer feedback is", fuzzer_feedback)
    #     passed_fuzzer = fuzzer_feedback is None
    # exit(0)

    # with open("test.txt", "w") as f:
    #     f.write(ps_text)

    # This is the function name to run. Will be updated once we pass the parser.
    func_name = None
    for i in range(max_num_tries):
        # First we get the previous solutions
        prev_solutions = [solutions[-1][0] for solutions in info]

        print(f"===== Starting iteration {i} =====")
        template_message = {"role": "user", "content": ps_text}

        if len(prev_solutions) > 0:
            all_prev_solutions = "\n".join(prev_solutions)
            messages_for_new_sol = [
                template_message,
                {"role": "assistant", "content": all_prev_solutions},
                {"role": "user", "content": TEMPLATE_ERR},
            ]
        else:
            messages_for_new_sol = [template_message]
        curr_solution = get_solution_from_llm(llm_model, messages_for_new_sol)
        info.append([])
        info[i].append((curr_solution, None))
        print("New solution is", curr_solution)

        # Now we try and fix this solution
        num_fixes = 0
        should_start_new_sol = False
        curr_fuzzer_feedback = None
        while num_fixes < max_num_tries_per_solution:
            if should_start_new_sol:
                break

            if curr_fuzzer_feedback is not None:
                print("Trying to fix the solution to pass fuzzer")
                messages_for_fuzzer = {
                    "role": "user",
                    "content": f"""
                    {ps_text}

                    <Generated solution>:
                    {curr_solution}

                    <Feedback>:
                    {curr_fuzzer_feedback}
                    """,
                }
                curr_solution = get_solution_from_llm(llm_model, [messages_for_fuzzer])
                print("New solution is", curr_solution)
                info[i].append((curr_solution, curr_fuzzer_feedback))
                num_fixes += 1

            # First pass through the parser
            passed_parser = False
            while not passed_parser and num_fixes < max_num_tries_per_solution:
                curr_parser_feedback = None
                try:
                    print("Passing solution to the parser")
                    func_names, _, _ = check_solution(curr_solution, 1)
                    func_name = func_names[0]
                    print("Parser solution passed the parser")
                    passed_parser = True
                except Exception as e:
                    print("Failed to pass the parser", e)
                    curr_parser_feedback = str(e)
                    messages_for_parser = [
                        template_message,
                        {"role": "assistant", "content": curr_solution},
                        {
                            "role": "user",
                            "content": curr_parser_feedback
                            + f"\nbe creative in trying to fix the solution"
                            + f"\n{TEMPLATE_ENCLOSE_CODE}",
                        },
                    ]
                    print("Trying to fix the solution to pass parser")
                    curr_solution = get_solution_from_llm(
                        llm_model, messages_for_parser
                    )
                    print("New solution is", curr_solution)
                    # Increment the number of fixes
                    num_fixes += 1
                    info[i].append((curr_solution, curr_parser_feedback))

            # Run the fuzzer. This does not take up a new try
            curr_fuzzer_feedback = _run_fuzzer_tests_and_get_messages(
                func_name=func_name, ps_sol=curr_solution, test_case_dir=test_case_dir
            )
            import pdb

            pdb.set_trace()

            if curr_fuzzer_feedback is None:
                print("All test cases passed, found correct solution")
                return info

            # At this point, we have made sure all num_fixes solutions have run fuzzer tests
            if num_fixes == max_num_tries_per_solution:
                print(f"Failed to find a solution after {max_num_tries_per_solution}")
                should_start_new_sol = True
                continue

    print("Failed to find a solution after all tries")
    return info


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--benchmark", type=str)
    args = parser.parse_args()

    TENSPILER_LLM_PATH = Path(__file__).parent.parent.resolve()
    BENCHMARKS_PATH = TENSPILER_LLM_PATH / "benchmarks"
    DSL_CODE_PATH = TENSPILER_LLM_PATH / "python_dsl.py"

    with open("tenspiler/llm/python_dsl.py") as f:
        dsl_code = f.read()

    all_suites = {"blend", "llama", "polybench"}
    for suite in all_suites:
        for file in (BENCHMARKS_PATH / suite).rglob("*.cc"):
            if args.benchmark is not None and args.benchmark not in file.name:
                continue
            print("--------------------------")
            print(f"Running benchmark {file.stem} in suite {suite}")
            with open(file) as f:
                source_code = f.read()

            info = run_llm(
                llm_model=LLMModel.CLAUDE,
                benchmark_name=file.stem,
                dsl_code=dsl_code,
                source_code=source_code,
                test_case_dir=Path(
                    f"/Users/jieq/Downloads/outputs_llama_3/{file.stem}"
                ),
            )
            with open(f"{file.stem}.json", "w") as f:
                json.dump(info, f, indent=2)
