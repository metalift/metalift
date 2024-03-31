import argparse
import json
import os
import re
from dataclasses import dataclass
from typing import List

from openai import OpenAI


@dataclass
class SingleLoopInfo:
    loop_var: str
    read_vars: List[str]
    modified_vars: List[str]


@dataclass
class OuterLoopInfo:
    outer_loop_var: str
    inner_loop_var: str
    outer_loop_read_vars: List[str]
    inner_loop_read_vars: List[str]
    outer_loop_modified_vars: List[str]
    inner_loop_modified_vars: List[str]


loop_info_map = {
    "softmax_part1": SingleLoopInfo(
        outer_loop_var="i", outer_loop_modified_vars=["max_val"]
    ),
    "softmax_part2": SingleLoopInfo(
        outer_loop_var="i", outer_loop_modified_vars=["cur", "output"]
    ),
    "softmax_part3": SingleLoopInfo(
        outer_loop_var="i", outer_loop_modified_vars=["sum"]
    ),
    "softmax_part4": SingleLoopInfo(
        outer_loop_var="i", outer_loop_modified_vars=["unnormalized_output"]
    ),
}

client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))

# reading arguments from the command line
parser = argparse.ArgumentParser()
parser.add_argument("--filename", type=str)
parser.add_argument("--source-code", type=str)
parser.add_argument("--dsl-code", type=str)
parser.add_argument("--n-choices", type=int, default=10)
# parser.add_argument("--post-cond", type=str)
args = parser.parse_args()

# dir = f"./benchmarks/dexter/outputs_invariants_constraints_pythonic_structure_nodefine/openai/{args.n_choices}_choices"
# TODO(jie)
dir = f"./benchmarks/llama/outputs/inv/{args.n_choices}/"
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
def invariant1(row, col, base, active, row_vec, out):
    return row op expr() and row op expr() and col op expr() and col op expr() and row_vec = operation over defined functions and out = operation over defined functions
```
```
def invariant2(row, active, base, out):
    return row op expr() and row op expr() and out = operation over defined_functions
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

outputs = client.chat.completions.create(
    model="gpt-4",  # model to use
    messages=[
        {"role": "system", "content": TEMPLATE_SYS},
        {"role": "user", "content": TEMPLATE_TEXT},
    ],
    # TODO(jie): 10 and 100
    n=args.n_choices,  # number of candidates,
    temperature=0.7,
)


def extract(s):
    return [x for x in re.findall(r"```(?:python|Python)?(.*)```", s, re.DOTALL)]


# extract the code from the completions
for idx, c in enumerate(outputs.choices):
    out = extract(c.message.content)
    # out = c.message.content
    # if not out:
    #     import pdb; pdb.set_trace()
    if out:
        print(f"{idx}")
        print(out[0])
        # print(c.message.content)
    print("=====")


if not os.path.exists(dir):
    os.makedirs(dir)

# saving prompt and completions to a file
with open(f"{dir}/{filename}.json", "w") as f:
    json.dump([c.message.content for c in outputs.choices], f, indent=4)

with open(f"{dir}/prompt_{filename}.txt", "w") as f:
    f.write(TEMPLATE_TEXT)
