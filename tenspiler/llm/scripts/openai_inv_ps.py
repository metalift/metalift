import argparse
import json
import os
import re
import textwrap
from dataclasses import dataclass
from typing import List as pyList
from typing import Union, get_args

from openai import OpenAI

from metalift.ir import Int, List, Var


@dataclass
class SingleLoopInfo:
    loop_var: Var
    read_vars: pyList[Var]
    modified_vars: pyList[Var]


@dataclass
class DoubleLoopInfo:
    outer_loop_var: Var
    inner_loop_var: Var
    outer_loop_read_vars: pyList[Var]
    inner_loop_read_vars: pyList[Var]
    outer_loop_modified_vars: pyList[Var]
    inner_loop_modified_vars: pyList[Var]


loop_info_map = {
    "softmax_part1": SingleLoopInfo(
        loop_var=Int("i").src,
        modified_vars=[Int("max_val").src],
        read_vars=[List(Int, "input").src, Int("max_pos").src],
    ),
    "softmax_part2": SingleLoopInfo(
        loop_var=Int("i").src,
        modified_vars=[Int("cur").src, Int("output").src],
        read_vars=[List(Int, "input").src, Int("max_pos").src, Int("max_val").src],
    ),
    "softmax_part3": SingleLoopInfo(
        loop_var=Int("i").src,
        modified_vars=[Int("sum").src],
        read_vars=[List(Int, "output").src, Int("max_pos").src],
    ),
    "softmax_part4": SingleLoopInfo(
        loop_var=Int("i").src,
        modified_vars=[List(Int, "unnormalized_output").src],
        read_vars=[
            List(Int, "unnormalized_output").src,
            Int("max_pos").src,
            Int("sum").src,
        ],
    ),
    "rmsnorm_part1": SingleLoopInfo(
        loop_var=Int("i").src,
        read_vars=[List(Int, "input").src, List(Int, "weight").src],
        modified_vars=[Int("ss").src],
    ),
    "rmsnorm_part2": SingleLoopInfo(
        loop_var=Int("i").src,
        read_vars=[List(Int, "input").src, List(Int, "weight").src, Int("ss").src],
        modified_vars=[List(Int, "output").src],
    ),
    "matmul": DoubleLoopInfo(
        outer_loop_var=Int("row").src,
        inner_loop_var=Int("col").src,
        outer_loop_read_vars=[List(Int, "weight").src, List(Int, "input").src],
        inner_loop_read_vars=[
            List(Int, "weight").src,
            List(Int, "input").src,
            List(Int, "output").src,
            Int("row").src,
        ],
        outer_loop_modified_vars=[List(Int, "output").src, Int("curr").src],
        inner_loop_modified_vars=[Int("curr").src],
    ),
    "transformer_part1": DoubleLoopInfo(
        outer_loop_var=Int("timestep").src,
        inner_loop_var=Int("i").src,
        outer_loop_read_vars=[
            Int("token_position").src,
            Int("head").src,
            Int("head_size").src,
            List(Int, "q").src,
            List(List[Int], "key_cache_layer").src,
        ],
        inner_loop_read_vars=[
            Int("token_position").src,
            Int("head").src,
            Int("head_size").src,
            List(Int, "q").src,
            List(List[Int], "key_cache_layer").src,
            Int("timestep").src,
        ],
        outer_loop_modified_vars=[List(Int, "attention").src, Int("score").src],
        inner_loop_modified_vars=[Int("score").src],
    ),
    "transformer_part2": DoubleLoopInfo(
        outer_loop_var=Int("i").src,
        inner_loop_var=Int("timestep").src,
        outer_loop_read_vars=[
            Int("token_position").src,
            Int("head").src,
            Int("head_size").src,
            List(List[Int], "key_cache_layer").src,
            List(Int, "attention").src,
        ],
        inner_loop_read_vars=[
            Int("token_position").src,
            Int("head").src,
            Int("head_size").src,
            List(List[Int], "key_cache_layer").src,
            List(Int, "attention").src,
        ],
        outer_loop_modified_vars=[List(Int, "xb").src, Int("curr").src],
        inner_loop_modified_vars=[Int("curr").src],
    ),
    "transformer_part3": SingleLoopInfo(
        loop_var=Int("i").src,
        read_vars=[List(Int, "input").src, Int("hidden_dim").src],
        modified_vars=[List(Int, "output").src, Int("curr").src],
    ),
    "transformer_part4": SingleLoopInfo(
        loop_var=Int("i").src,
        read_vars=[List(Int, "input1").src, List(Int, "input2").src],
        modified_vars=[List(Int, "output").src],
    ),
}


def generate_invariant_template(
    loop_info: Union[SingleLoopInfo, DoubleLoopInfo]
) -> str:
    if isinstance(loop_info, SingleLoopInfo):
        arguments = sorted(
            list(
                set(
                    loop_info.read_vars + loop_info.modified_vars + [loop_info.loop_var]
                )
            ),
            key=lambda x: x.name(),
        )
        args_with_types = ", ".join(
            [
                f"{arg}: {arg.type.to_python_type_str(get_args(arg.type))}"
                for arg in arguments
            ]
        )
        loop_var = loop_info.loop_var.name()
        modified_vars_cond = " and ".join(
            [
                f"{var} == operation over defined functions"
                for var in loop_info.modified_vars
            ]
        )
        return textwrap.dedent(
            f"""
            def invariant({args_with_types}) -> bool:
                return {loop_var} op expr() and {loop_var} op expr() and {modified_vars_cond}
            """
        )
    else:
        outer_inv_args = sorted(
            list(
                set(
                    loop_info.outer_loop_read_vars
                    + loop_info.outer_loop_modified_vars
                    + [loop_info.outer_loop_var]
                )
            ),
            key=lambda x: x.name(),
        )
        outer_inv_args_with_types = ", ".join(
            [
                f"{arg}: {arg.type.to_python_type_str(get_args(arg.type))}"
                for arg in outer_inv_args
            ]
        )
        inner_inv_args = sorted(
            list(
                set(
                    loop_info.inner_loop_read_vars
                    + loop_info.inner_loop_modified_vars
                    + [loop_info.inner_loop_var]
                )
            ),
            key=lambda x: x.name(),
        )
        inner_inv_args_with_types = ", ".join(
            [
                f"{arg}: {arg.type.to_python_type_str(get_args(arg.type))}"
                for arg in inner_inv_args
            ]
        )
        outer_loop_var = loop_info.outer_loop_var.name()
        inner_loop_var = loop_info.inner_loop_var.name()
        outer_modified_vars_cond = " and ".join(
            [
                f"{var} == operation over defined functions"
                for var in loop_info.outer_loop_modified_vars
            ]
        )
        inner_modified_vars_cond = " and ".join(
            [
                f"{var} == operation over defined functions"
                for var in loop_info.inner_loop_modified_vars
            ]
        )
        outer_loop_var_cond = (
            f"{outer_loop_var} op expr() and {outer_loop_var} op expr()"
        )
        inner_loop_var_cond = f"{inner_loop_var} op expr() and {inner_loop_var} op expr() and {outer_loop_var_cond}"

        return textwrap.dedent(
            f"""
            def invariant1({outer_inv_args_with_types}) -> bool:
                return {outer_loop_var_cond} and {outer_modified_vars_cond}

            def invariant2({inner_inv_args_with_types}) -> bool:
                return {inner_loop_var_cond} and {inner_modified_vars_cond}
            """
        )


client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))

# reading arguments from the command line
parser = argparse.ArgumentParser()
parser.add_argument("--benchmark-suite", type=str)
parser.add_argument("--filename", type=str)
parser.add_argument("--source-code", type=str)
parser.add_argument("--dsl-code", type=str)
parser.add_argument("--n-choices", type=int, default=10)
# parser.add_argument("--post-cond", type=str)
args = parser.parse_args()

dir = f"/Users/jieq/Desktop/metalift/tenspiler/llm/benchmarks/{args.benchmark_suite}/outputs/openai/inv_ps/{args.n_choices}_choices"
filename = args.filename
source_code = open(args.source_code).read()
dsl_code = open(args.dsl_code).read()

# prompt for generating invariants of a function.
TEMPLATE_TEXT = f"""Your task is to rewrite the given `test` C++ Function. You need to use only the set of provided functions and constants to achieve this. The rewritten program should be semantically equivalent to the `test` function. In addition, your task is to prove that rewritten function is equivalent to the `test` function. We can prove this by finding a loop invariant using the defined functions. Write the loop invariant as a python boolean formula.
#Instructions Rewriting
# 1. Do not use for/while loops for rewriting the function.
# 2. The rewritten program should just be a single return statement of the form return_var = provided_function(...)
# 3. Inline all the expressions. Do not use intermediate variables.
#Instructions Invariants:
# 1. You need to use only the defined functions to write the loop invariant.
# 2. Do not use for/while loops for rewriting the function.
# 3. The rewritten program should just be a single return statement of the form return_var = provided_function(...)
# 4. Inline all the expressions. Do not use intermediate variables.
# 5. Generate separate loop invariants for each loop in the test function.
# 6. invariant structure
```
{generate_invariant_template(loop_info_map[filename])}
```

Example1:
```
#defined functions
def vec_elemwise_sub(x: list[int], y: list[int]) -> list[int]:
    return (
        []
        if len(x) < 1 or not len(x) == len(y)
        else [x[0] - y[0], *vec_elemwise_sub(x[1:], y[1:])]
    )
def matrix_elemwise_sub(matrix_x,: list[list[int]], matrix_y: list[list[int]]) -> list[list[int]]:
    return (
        []
        if len(matrix_x) < 1 or not len(matrix_x) == len(matrix_y)
        else [
            vec_elemwise_sub(matrix_x[0], matrix_y[0]),
            *matrix_elemwise_sub(matrix_x[1:], matrix_y[1:]),
        ]
    )
//test function
vector<vector<uint8_t>> test(vector<vector<uint8_t>> base, vector<vector<uint8_t>> active)
{{
    vector<vector<uint8_t>> out;
    uint8_t m = base.size();
    uint8_t n = base[0].size();
	for (uint8_t row = 0; row < m; row++) {{
        vector<uint8_t> row_vec;
		for (uint8_t col = 0; col < n; col++) {{
            uint8_t pixel = base[row][col] - active[row][col] ;
			row_vec.push_back(pixel);

		}}
		out.push_back(row_vec);
	}}
	return out
}}
def test(vector<vector<uint8_t>> base, vector<vector<uint8_t>> active)
    return out = matrix_elemwise_sub(base, active)
def invariant1(row, outer_loop_vars):
    return row >= 0 and row <= m and out == matrix_elemwise_sub(base[:row], active[:row])
def invariant2(row, col, inner_loop_vars, outer_loop_vars):
    return row >= 0 and row < m and col >= 0 and col <= n and row_vec == vec_elemwise_sub(base[row][:col], active[row][:col]) and out == matrix_elemwise_sub(base[:row], active[:row])
```

Example2:
```
#defined functions
{dsl_code}

//test function
{source_code}
```
"""

TEMPLATE_SYS = "You are a helpful expert in programming languages."

# sol = f"""
# # Loop invariant for the inner loop
# def invariant2(token_position, head, head_size, key_cache_layer, q, score, timestep, i):
#     return (i >= 0 and i <= head_size and timestep >= 0 and timestep <= token_position and
#             score == reduce_sum(vec_elemwise_mul(vec_slice(q, head * head_size, head * head_size + i),
#             vec_slice(matrix_row_slice(key_cache_layer, timestep, timestep + 1)[0], head * head_size, head * head_size + i))) / integer_sqrt(head_size * 1))
# """

outputs = client.chat.completions.create(
    model="gpt-4",  # model to use
    messages=[
        {"role": "system", "content": TEMPLATE_SYS},
        {"role": "user", "content": TEMPLATE_TEXT},
        # {"role": "assistant", "content": sol},
        # {"role": "user", "content": "This invariant is incorrect, generate another one."}
    ],
    n=args.n_choices,  # number of candidates,
    temperature=0.7,
)


def extract(s):
    return [x for x in re.findall(r"```(?:python|Python)?(.*?)```", s, re.DOTALL)]


raw_response_filename = f"{dir}/{filename}_ps_raw_response_before_extraction.json"
responses_before_extraction: pyList[str] = []
responses: pyList[str] = []

# extract the code from the completions
for idx, c in enumerate(outputs.choices):
    out = extract(c.message.content)
    if out:
        responses_before_extraction.append(c.message.content)
        print(idx)
        print("\n\n".join(out))
        responses.append("\n\n".join(out))
        # print(c.message.content)
    print("=====")

if not os.path.exists(dir):
    os.makedirs(dir)

json_response_file = open(f"{dir}/{filename}_ps_raw_response.json", "w")
json.dump({filename: responses}, json_response_file)
raw_response_file = open(raw_response_filename, "w")
json.dump({filename: responses_before_extraction}, raw_response_file)

# saving prompt and completions to a file
with open(f"{dir}/{filename}.json", "w") as f:
    json.dump([c.message.content for c in outputs.choices], f, indent=4)

with open(f"{dir}/prompt_{filename}.txt", "w") as f:
    f.write(TEMPLATE_TEXT)
