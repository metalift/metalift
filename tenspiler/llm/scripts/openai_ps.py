import argparse
import json
import os
import re
from typing import List

from openai import OpenAI

client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))


# reading arguments from the command line
parser = argparse.ArgumentParser()
parser.add_argument("--benchmark-suite", type=str)
parser.add_argument("--filename", type=str)
parser.add_argument("--source-code", type=str)
parser.add_argument("--dsl-code", type=str)
parser.add_argument("--n-choices", type=int, default=10)
args = parser.parse_args()

dir = f"./benchmarks/{args.benchmark_suite}/outputs/openai/ps/{args.n_choices}_choices"
filename = args.filename
source_code = open(args.source_code).read()
dsl_code = open(args.dsl_code).read()


# prompt for guessing the post conditions of a function. dsl_code is the set of functions and constants that can be used to rewrite the function. source_code is the function to be rewritten.
TEMPLATE_TEXT = f"""
Your task is to rewrite the given `test` C++ Function. You need to use only the set of provided functions and constants to achieve this. The rewritten program should be semantically equivalent to the `test` function. Please do not generate any explanations.
#Instructions
# 1. Do not use for/while loops for rewriting the function.
# 2. The rewritten program should just be a single return statement of the form return_var = provided_function(...)
# 3. Inline all the expressions. Do not use intermediate variables.
```
#defined functions
{dsl_code}
```
```
//test function
{source_code}
```
"""

TEMPLATE_SYS = "You are a helpful expert in programming languages."
import pdb

pdb.set_trace()

# call the completions endpoint to get the completions for the prompt
outputs = client.chat.completions.create(
    model="gpt-4",  # model to use
    messages=[
        {"role": "system", "content": TEMPLATE_SYS},
        {"role": "user", "content": TEMPLATE_TEXT},
    ],
    n=args.n_choices,  # number of candidates,
    temperature=0.7,
)


# regex to extract the code from the completions
def extract(s):
    return [
        x for x in re.findall(r"```(?:Python|python|assembly)?(.*?)```", s, re.DOTALL)
    ]


raw_response_filename = f"{dir}/{filename}_ps_raw_response.txt"
raw_response_file = open(raw_response_filename, "a")

json_response_file = open(f"{dir}/{filename}_ps_raw_response.json", "w")
responses: List[str] = []


# extract the code from the completions
for idx, c in enumerate(outputs.choices):
    out = extract(c.message.content)
    if out:
        print(f"{idx}")
        print(c.message.content, file=raw_response_file)
        print(out[0])
        responses.append(out[0])
    print("=====")

json.dump({filename: responses}, json_response_file)


if not os.path.exists(dir):
    os.makedirs(dir)

# saving prompt and completions to a file
with open(f"{dir}/{filename}.json", "w") as f:
    json.dump([c.message.content for c in outputs.choices], f, indent=4)

with open(f"{dir}/prompt_{filename}.txt", "w") as f:
    f.write(TEMPLATE_TEXT)
