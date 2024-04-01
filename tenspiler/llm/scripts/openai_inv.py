import argparse
import json
import os
import re
import textwrap
from dataclasses import dataclass
from typing import List, Union

from openai import OpenAI


@dataclass
class SingleLoopInfo:
    loop_var: str
    read_vars: List[str]
    modified_vars: List[str]


@dataclass
class DoubleLoopInfo:
    outer_loop_var: str
    inner_loop_var: str
    outer_loop_read_vars: List[str]
    inner_loop_read_vars: List[str]
    outer_loop_modified_vars: List[str]
    inner_loop_modified_vars: List[str]


loop_info_map = {
    "softmax_part1": SingleLoopInfo(
        loop_var="i", modified_vars=["max_val"], read_vars=["input", "max_pos"]
    ),
    "softmax_part2": SingleLoopInfo(
        loop_var="i",
        modified_vars=["cur", "output"],
        read_vars=["input", "max_pos", "max_val"],
    ),
    "softmax_part3": SingleLoopInfo(
        loop_var="i", modified_vars=["sum"], read_vars=["output", "max_pos"]
    ),
    "softmax_part4": SingleLoopInfo(
        loop_var="i",
        modified_vars=["unnormalized_output"],
        read_vars=["unnormalized_output", "max_pos", "sum"],
    ),
    "rmsnorm_part1": SingleLoopInfo(
        loop_var="i", read_vars=["input", "weight"], modified_vars=["ss"]
    ),
    "rmsnorm_part2": SingleLoopInfo(
        loop_var="i", read_vars=["input", "weight", "ss"], modified_vars=["output"]
    ),
    "matmul": DoubleLoopInfo(
        outer_loop_var="row",
        inner_loop_var="col",
        outer_loop_read_vars=["weight", "input"],
        inner_loop_read_vars=["weight", "input", "output", "row"],
        outer_loop_modified_vars=["output", "curr"],
        inner_loop_modified_vars=["curr"],
    ),
    "transformer_part1": DoubleLoopInfo(
        outer_loop_var="timestep",
        inner_loop_var="i",
        outer_loop_read_vars=[
            "token_position",
            "head",
            "head_size",
            "q",
            "key_cache_layer",
        ],
        inner_loop_read_vars=[
            "token_position",
            "head",
            "head_size",
            "q",
            "key_cache_layer",
            "timestep",
        ],
        outer_loop_modified_vars=["attention", "score"],
        inner_loop_modified_vars=["score"],
    ),
    "transformer_part2": DoubleLoopInfo(
        outer_loop_var="i",
        inner_loop_var="timestep",
        outer_loop_read_vars=[
            "token_position",
            "head",
            "head_size",
            "key_cache_layer",
            "attention",
        ],
        inner_loop_read_vars=[
            "token_position",
            "head",
            "head_size",
            "key_cache_layer",
            "attention",
        ],
        outer_loop_modified_vars=["xb", "curr"],
        inner_loop_modified_vars=["curr"],
    ),
    "transformer_part3": SingleLoopInfo(
        loop_var="i",
        read_vars=["input", "hidden_dim"],
        modified_vars=["output", "curr"],
    ),
    "transformer_part4": SingleLoopInfo(
        loop_var="i", read_vars=["input1", "input2"], modified_vars=["output"]
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
            )
        )
        loop_var = loop_info.loop_var
        modified_vars_cond = " and ".join(
            [
                f"{var} == operation over defined functions"
                for var in loop_info.modified_vars
            ]
        )
        return textwrap.dedent(
            f"""
            def invariant({', '.join(arguments)}):
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
            )
        )
        inner_inv_args = sorted(
            list(
                set(
                    loop_info.inner_loop_read_vars
                    + loop_info.inner_loop_modified_vars
                    + [loop_info.inner_loop_var]
                )
            )
        )
        outer_loop_var = loop_info.outer_loop_var
        inner_loop_var = loop_info.inner_loop_var
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
            def invariant1({', '.join(outer_inv_args)}):
                return {outer_loop_var_cond} and {outer_modified_vars_cond}

            def invariant2({', '.join(inner_inv_args)}):
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

dir = f"./benchmarks/{args.benchmark_suite}/outputs/openai/inv/{args.n_choices}_choices"
filename = args.filename
source_code = open(args.source_code).read()
dsl_code = open(args.dsl_code).read()

# reading post-conditions
file = "/Users/jieq/Desktop/metalift/tenspiler/llm/benchmarks/llama/source/ps.json"
post_conds = json.load(open(file))


# find the return statement in the source code and replace with assert post-cond
lines = source_code.split("\n")
for idx, line in enumerate(lines):
    if "return" in line:
        # split the line into return and the expression
        return_stmt = line.split("return")
        # strip ";"
        return_var = return_stmt[-1].strip()
        return_var = return_var[:-1] if return_var[-1] == ";" else return_var
        # replace the return statement with the assert statement
        lines[idx] = f"assert {return_var} == {post_conds[filename]}"
        break
source_code = "\n".join(lines)


# prompt for generating invariants of a function.
TEMPLATE_TEXT = f"""Your task is to prove that `assertion` is true in the `test` function. The assertion can proved by finding a loop invariant using the defined functions. Write the loop invariant as a python boolean formula.

#Instructions:
1. You need to use only the defined functions to write the loop invariant.
2. Do not use for/while loops for rewriting the function.
3. The rewritten program should just be a single return statement of the form return_var = provided_function(...)
4. Inline all the expressions. Do not use intermediate variables.
5. Generate separate loop invariants for each loop in the test function.
6. invariant structure
```
{generate_invariant_template(loop_info_map[filename])}
```

Example1:
```
#defined functions
def map(data: List[int] , f: func):
    return [f(x) for x in data]
def reduce(data: List[int] , f: func):
    if len(data) == 0:
        return 0
    else:
        return f(data[0], reduce(data[1:], f))
def add(a: int , b: int):
    return a + b
constants = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
#test function
def test(data: List[int]):
    count = 0
    for i in range(len(data)):
        count += 1
    assert count == reduce(map(data, lambda x: 1), add)
def invariant(data: List[int], count: int, i:int):
    return i >= 0 and i <= len(data) and count == reduce(map(data[:i], lambda x: 1), add)
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
raw_response_file = open(raw_response_filename, "w")
responses_before_extraction: List[str] = []
json_response_file = open(f"{dir}/{filename}_ps_raw_response.json", "w")
responses: List[str] = []

# extract the code from the completions
for idx, c in enumerate(outputs.choices):
    out = extract(c.message.content)
    if out:
        responses_before_extraction.append(c.message.content)
        responses.append("\n\n".join(out))
        # print(c.message.content)
    print("=====")

json.dump({filename: responses}, json_response_file)
json.dump({filename: responses_before_extraction}, raw_response_file)
exit(0)

if not os.path.exists(dir):
    os.makedirs(dir)

# saving prompt and completions to a file
with open(f"{dir}/{filename}.json", "w") as f:
    json.dump([c.message.content for c in outputs.choices], f, indent=4)

with open(f"{dir}/prompt_{filename}.txt", "w") as f:
    f.write(TEMPLATE_TEXT)
