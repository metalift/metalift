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
    _generate_invariant_template,
    _loop_info_map,
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
    import pdb

    pdb.set_trace()
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
    raw_solution = extract(response.text)[0]
    print("Raw response", response.text)
    extracted_solution = replace_ite(raw_solution)
    print("Extracted response", extracted_solution)
    return extracted_solution


def get_solution_from_claude(messages: list[dict[str, Any]]) -> str:
    print("running with claude")
    message = claude_client.messages.create(
        model="claude-3-5-sonnet-20240620",
        max_tokens=1000,
        temperature=0.7,
        system=TEMPLATE_SYS,
        messages=messages,
    )
    raw_solutions = extract(message.content[0].text)
    return [replace_ite(raw_solution) for raw_solution in raw_solutions]


def get_inv(suite_name: str, benchmark_name: str, dsl_code: str) -> None:
    # TODO(jie): move this to utils
    with open(f"tenspiler/llm/inv_code/{suite_name}/{benchmark_name}.txt") as f:
        inv_code_with_assert = f.read()
    single_loop_inv_text = f"""
    Your task is to generate the loop invariant `Inv` such that it is true at all the locations it is defined at.  Generate only a single `Inv` expression which holds at all the locations. The invariant needs to be generated using only the functions defined below. Write the loop invariant as a python boolean formula.
    #Instructions:
    1. You can use the defined functions to write the loop invariant. Do not use any for loops or any other python construct.
    2. Generate separate loop invariants for each loop in the test function. Return the loop invariant as a single boolean expression. Only return the invariant and no other code in a code block.
    Example1:

    {dsl_code}

    //test function
    {inv_code_with_assert}

    ```
    Use the following template to generate the loop invariant
    ```

    # A strong loop invariant should have the following properties:
    # 1. It should have boolean expressions over the loop index variable `i` to describe the valid range of `i`.
    # 2. It should have an inductive expression describing the output variable `out` using the defined functions.
    {_generate_invariant_template(benchmark_name)}
    ```
    """
    double_loop_info = _loop_info_map[benchmark_name]
    outer_loop_var = double_loop_info.outer_loop_var.name()
    inner_loop_var = double_loop_info.inner_loop_var.name()
    outer_loop_modified_vars = double_loop_info.outer_loop_modified_vars
    assert len(outer_loop_modified_vars) == 1
    inner_modified_vars_not_in_outer = [
        var
        for var in double_loop_info.inner_loop_modified_vars
        if var not in outer_loop_modified_vars
    ]
    assert len(inner_modified_vars_not_in_outer) == 1
    inner_modified_var = inner_modified_vars_not_in_outer[0].name()

    rv_var = outer_loop_modified_vars[0].name()
    outer_inv, inner_inv = _generate_invariant_template(benchmark_name)
    double_loop_inv_text = f"""
    Your task is to generate two loop invariants `invariant1` and `invariant2` such that the given assertion holds. The invariants need to be generated using only the functions defined below. Write the loop invariants as python boolean formulas.

    #Instructions:
    1. You can use the defined functions to write the loop invariant. Do not use any for loops or any other python construct such as list comprehensions or the `all` function.
    2. Generate separate loop invariants for each loop in the test function. Return the loop invariant as a single boolean expression. Only return the invariant and no other code.

    ```
    #defined functions
    {dsl_code}

    //test function
    {inv_code_with_assert}
    ```

    Use the following template to generate the outer loop invariant
    ```
    # A strong loop invariant should have the following properties:
    # 1. It should have boolean expressions over the loop index variable `{outer_loop_var}` to describe the valid range of `{outer_loop_var}`.
    # 2. It should have an inductive expression describing the output variable `{rv_var}` using the defined functions.
    {outer_inv}

    Use the following template to generate the inner loop invariant
    # A strong loop invariant should have the following properties:
    # 1. It should have boolean expressions over the loop index variable `{outer_loop_var}` to describe the valid range of `{outer_loop_var}` and the loop index variable `{inner_loop_var}` to describe the valid range of `{inner_loop_var}`.
    # 2. It should have an inductive expression describing the output variable `{rv_var}` using the defined functions and `{inner_modified_var}` variable.
    {inner_inv}
    ```
    """
    with open(f"{benchmark_name}.txt", "w") as f:
        f.write(double_loop_inv_text)
    return double_loop_inv_text


def get_solution_from_gpt(messages: list[dict[str, Any]]) -> str:
    print("running with gpt")
    # messages don't include the system message
    import pdb

    pdb.set_trace()
    messages_with_sys = [{"role": "system", "content": TEMPLATE_SYS}, *messages]
    outputs = openai_client.chat.completions.create(
        model="gpt-4o-2024-08-06",  # model to use
        messages=messages_with_sys,
        n=1,
        temperature=0.7,
    )
    outputs = [choice.message.content for choice in outputs.choices]
    raw_output = extract(outputs[0])[0]
    extracted_output = replace_ite(raw_output)
    print("Raw output", raw_output)
    print("Extracted output", extracted_output)
    return extracted_output


# Define all the clients that are needed
openai_client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))
claude_client = anthropic.Anthropic(api_key=os.getenv("CLAUDE_API_KEY"))


def run_llm(
    *,
    llm_model: LLMModel,
    benchmark_name: str,
    suite_name: str,
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
    with open(f"{benchmark_name}.txt", "w") as f:
        f.write(ps_text)
        f.flush()

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
                fuzzer_message_content = f"""
                {ps_text}

                <Generated solution>:
                {curr_solution}

                <Feedback>:
                {curr_fuzzer_feedback}
                """
                print("Fuzzer message content", fuzzer_message_content)
                messages_for_fuzzer = {
                    "role": "user",
                    "content": fuzzer_message_content,
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
                    print("Parser message content is", curr_parser_feedback)
                    content = (
                        curr_parser_feedback
                        + f"\nbe creative in trying to fix the solution"
                        + f"\n{TEMPLATE_ENCLOSE_CODE}"
                    )
                    messages_for_parser = [
                        template_message,
                        {"role": "assistant", "content": curr_solution},
                        {
                            "role": "user",
                            "content": content,
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
                llm_model=LLMModel.GEMINI,
                benchmark_name=file.stem,
                suite_name=suite,
                dsl_code=dsl_code,
                source_code=source_code,
                test_case_dir=Path(
                    f"/Users/jieq/Downloads/outputs_{suite}_3/{file.stem}"
                ),
            )
            with open(f"{file.stem}.json", "w") as f:
                json.dump(info, f, indent=2)
