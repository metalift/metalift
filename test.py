import json
from pathlib import Path
from typing import List

from tenspiler.llm.python_dsl import (
    integer_sqrt,
    matrix_col_slice,
    matrix_vec_mul,
    reduce_max,
    vec_scalar_div,
    vec_slice,
)


def softmax_part1(input: List[int], max_pos: int) -> int:
    return reduce_max(vec_slice(input, 0, max_pos))


sol = f"""
def transformer_part3(input: List[int], hidden_dim: int) -> List[int]:
    return vec_elemwise_mul(
        input[:hidden_dim],
        scalar_vec_div(1, vec_scalar_add(1, vec_map(vec_scalar_mul(-1, input[:hidden_dim]), integer_exp)))
    )
"""


def transformer_part1(
    token_position: int,
    head: int,
    head_size: int,
    key_cache_layer: List[List[int]],
    q: List[int],
) -> List[int]:
    return vec_scalar_div(
        integer_sqrt(head_size * 1),
        matrix_vec_mul(
            matrix_col_slice(key_cache_layer, head * head_size, (head + 1) * head_size),
            vec_slice(q, head * head_size, (head + 1) * head_size),
        )[:token_position],
    )


def transformer_part1_baseline(
    token_position: int,
    head: int,
    head_size: int,
    key_cache_layer: List[List[int]],
    q: List[int],
) -> List[int]:
    attention = []
    for timestep in range(token_position):
        score = 0
        for i in range(head_size):
            score += (
                q[head * head_size + i]
                * key_cache_layer[timestep][head * head_size + i]
            )
        score //= integer_sqrt(head_size * 1)
        attention.append(score)
    return attention


data = {
    "head": 0,
    "head_size": 3,
    "token_position": 2,
    "key_cache_layer": [[1, 2, 3, 4], [5, 6, 7, 8]],
    "q": [1, 2, 3, 4],
}
print(transformer_part1(**data))
print(transformer_part1_baseline(**data))
exit(0)

test_case_dir = Path("/Users/jieq/Downloads/outputs_llama_3/transformer_part1")
for test_case_file in test_case_dir.rglob("*.json"):
    with open(test_case_file) as f:
        try:
            test_data = json.load(f)
        except:
            print("Skipping file", test_case_file)
            continue
        expected = test_data["result"]
        del test_data["result"]
        error = None
        try:
            actual = transformer_part1(**test_data)
        except Exception as e:
            error = str(e)
            actual = None
        if actual != expected or error is not None:
            print(test_data, expected)
            import pdb

            pdb.set_trace()
            print("Mismatch in", test_case_file)
            print("Expected:", expected)
            if error is not None:
                print("Error:", error)
            else:
                print("Actual:", actual)
            print()
