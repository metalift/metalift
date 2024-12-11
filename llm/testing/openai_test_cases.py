import json
from textwrap import dedent

from llm.parser import check_solution, remove_comments

outputs_mapping = {
    "color_burn_8": [
        [[31, 29], [30, 30]],
        [[0, 32], [16, 24]],
        [[21, 22], [29, 32]],
        [[32, 28], [29, 32]],
        [[31, 29], [30, 32]],
        [[32, 10], [24, 29]],
        [[32, 32], [32, 34]],
    ],
    "transformer_part1": [[1], [4, 10], [2, 8, 14], [5, 19], [85, 210, 335]],
    "transformer_part2": [[11], [34, 40], [60, 70, 80], [21], [42, 48]],
    "fdtd_2d_part2": [
        [[2, 3], [0, 11]],
        [[-5, -5, -5], [6, 6, 6], [2, 2, 2]],
        [[1]],
        [[3, 4], [16, 17]],
        [[-1], [6]],
    ],
}
inputs_mapping = {
    "color_burn_8": [
        {"base": [[30, 20], [10, 5]], "active": [[2, 4], [8, 10]]},
        {"base": [[0, 32], [16, 24]], "active": [[1, 1], [1, 1]]},
        {"base": [[10, 0], [15, 32]], "active": [[2, 3], [5, 8]]},
        {"base": [[31, 1], [2, 30]], "active": [[5, 7], [9, 11]]},
        {"base": [[16, 8], [24, 32]], "active": [[16, 8], [4, 2]]},
        {"base": [[5, 10], [15, 20]], "active": [[0, 1], [2, 4]]},
        {"base": [[10, 20], [30, 40]], "active": [[32, 16], [8, 4]]},
    ],
    "transformer_part1": [
        {
            "token_position": 1,
            "head": 0,
            "head_size": 1,
            "key_cache_layer": [[1, 2], [3, 4]],
            "q": [1, 2],
        },
        {
            "token_position": 2,
            "head": 1,
            "head_size": 1,
            "key_cache_layer": [[1, 2, 3], [4, 5, 6], [7, 8, 9]],
            "q": [1, 2, 3],
        },
        {
            "token_position": 3,
            "head": 0,
            "head_size": 2,
            "key_cache_layer": [
                [1, 2, 3, 4],
                [5, 6, 7, 8],
                [9, 10, 11, 12],
                [13, 14, 15, 16],
            ],
            "q": [1, 2, 3, 4],
        },
        {
            "token_position": 2,
            "head": 0,
            "head_size": 2,
            "key_cache_layer": [[1, 2, 3, 4], [5, 6, 7, 8], [9, 10, 11, 12]],
            "q": [4, 3, 2, 1],
        },
        {
            "token_position": 3,
            "head": 1,
            "head_size": 2,
            "key_cache_layer": [
                [10, 20, 30, 40, 50],
                [60, 70, 80, 90, 100],
                [110, 120, 130, 140, 150],
                [160, 170, 180, 190, 200],
            ],
            "q": [5, 4, 3, 2, 1],
        },
    ],
    "transformer_part2": [
        {
            "token_position": 1,
            "head": 0,
            "head_size": 1,
            "key_cache_layer": [[1, 2], [3, 4]],
            "attention": [2, 3],
        },
        {
            "token_position": 2,
            "head": 1,
            "head_size": 2,
            "key_cache_layer": [[1, 2, 3, 4], [5, 6, 7, 8], [9, 10, 11, 12]],
            "attention": [3, 2, 1],
        },
        {
            "token_position": 3,
            "head": 0,
            "head_size": 3,
            "key_cache_layer": [
                [1, 2, 3, 4, 5],
                [6, 7, 8, 9, 10],
                [11, 12, 13, 14, 15],
                [16, 17, 18, 19, 20],
            ],
            "attention": [4, 3, 2, 1],
        },
        {
            "token_position": 1,
            "head": 2,
            "head_size": 1,
            "key_cache_layer": [[1, 2, 3], [4, 5, 6], [7, 8, 9]],
            "attention": [1, 3, 2],
        },
        {
            "token_position": 2,
            "head": 1,
            "head_size": 2,
            "key_cache_layer": [[2, 4, 6, 8], [10, 12, 14, 16], [18, 20, 22, 24]],
            "attention": [1, 1, 1],
        },
    ],
    "fdtd_2d_part2": [
        {"nx": 2, "ny": 3, "ex": [[1, 2, 3], [4, 5, 6]], "hz": [[1, 1, 1], [0, 1, 0]]},
        {
            "nx": 3,
            "ny": 4,
            "ex": [[0, 0, 0, 0], [1, 1, 1, 1], [2, 2, 2, 2]],
            "hz": [[1, 2, 3, 4], [4, 3, 2, 1], [0, 0, 0, 0]],
        },
        {"nx": 1, "ny": 2, "ex": [[5, 6]], "hz": [[1, 2]]},
        {
            "nx": 2,
            "ny": 3,
            "ex": [[7, 8, 9], [10, 11, 12]],
            "hz": [[1, 2, 3], [3, 2, 1]],
        },
        {"nx": 2, "ny": 2, "ex": [[3, 4], [5, 6]], "hz": [[2, 3], [1, 1]]},
    ],
}


def run_test(func_name: str, ps_sol: str) -> int:
    universal_imports = f"""
    from llm.python_dsl import *
    from typing import Any, Callable, List
    """
    ps_sol = dedent(remove_comments(dedent(universal_imports) + dedent(ps_sol)))
    namespace = {}
    exec(ps_sol, namespace)
    inputs = inputs_mapping[func_name]
    expected_outputs = outputs_mapping[func_name]
    assert len(inputs) == len(
        expected_outputs
    ), f"expected {len(inputs)} outputs, but got {len(expected_outputs)}"

    passed_count = 0
    for input, expected_output in zip(inputs, expected_outputs):
        try:
            actual = namespace[func_name](**input)
            assert (
                actual == expected_output
            ), f"expected {expected_output}, but got {actual}"
            passed_count += 1
        except:
            continue

    return passed_count


exceptions_count: dict[str, int] = {}
num_passed_test_cases: dict[str, list[int]] = {"passed_parser": [], "failed_parser": []}

if __name__ == "__main__":
    filename = "tenspiler/llm/testing/ps_sols/fdtd_2d_part2_ps.json"
    seen_ps_sols = set()
    with open(filename, "r") as f:
        ps_sols = json.load(f)
    for idx, ps_sol in enumerate(ps_sols):
        print(f"------{idx}th PS solution--------")
        print(ps_sol)

        if ps_sol in seen_ps_sols:
            print("Skipping duplicate solution")
            print()
            continue
        seen_ps_sols.add(ps_sol)

        # If we passed the parser, we run tests
        passed_count = run_test("fdtd_2d_part2", ps_sol)
        print(f"Passed {passed_count} tests")

        try:
            ps_fn_decls, ps_in_calls = check_solution(ps_sol, 1)
            print("Parsed PS solution")
            num_passed_test_cases["passed_parser"].append(passed_count)
        except Exception as e:
            print(f"Failed to parse PS solution {e}")
            exceptions_count[str(e)] = exceptions_count.get(str(e), 0) + 1
            num_passed_test_cases["failed_parser"].append(passed_count)

    for k, v in exceptions_count.items():
        print(f"{k}: {v}")

    for k, v in num_passed_test_cases.items():
        print(f"{k}: {v}")
