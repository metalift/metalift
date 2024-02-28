import argparse
import json
import os
import re

import google.generativeai as genai

genai.configure(api_key="AIzaSyAQTWOYCWSzuDNhbeXOggQisCT4AqAnthE")


# reading arguments from the command line
parser = argparse.ArgumentParser()
parser.add_argument("--filename", type=str)
parser.add_argument("--source-code", type=str)
parser.add_argument("--dsl-code", type=str)
args = parser.parse_args()

dir = f"./benchmarks/dexter/outputs/gemini/"
filename = args.filename
source_code = open(args.source_code).read()
dsl_code = open(args.dsl_code).read()


model = genai.GenerativeModel("gemini-pro")

# prompt for guessing the post conditions of a function. dsl_code is the set of functions and constants that can be used to rewrite the function. source_code is the function to be rewritten.
TEMPLATE_TEXT = f"""
Your task is to rewrite the given `test` C++ Function. You need to use only the set of provided functions and constants to achieve this. The rewritten program should be semantically equivalent to the `test` function.
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

# call the completions endpoint to get the completions for the prompt
completion = model.generate_content(
    TEMPLATE_TEXT,
    generation_config=genai.types.GenerationConfig(
        # Only one candidate for now.
        max_output_tokens=5000,
        temperature=0.9,
        candidate_count=1,
    ),
)


# regex to extract the code from the completions
def extract(s):
    return [x for x in re.findall(r"```(?:python|assembly)?(.*)```", s, re.DOTALL)]


if not os.path.exists(dir):
    os.makedirs(dir)

# TODO(jie): extract this code
for i in range(10):
    choices = extract(completion.candidates[0].content.parts[0].text)

    # extract the code from the completions
    for _, c in enumerate(choices):
        print(f"{i}")
        print(c)
        print("=====")

    # saving prompt and completions to a file
    with open(f"{dir}/{filename}_try_{i}.json", "w") as f:
        json.dump([completion.candidates[0].content.parts[0].text], f, indent=4)

    with open(f"{dir}/prompt_{filename}_try_{i}.txt", "w") as f:
        f.write(TEMPLATE_TEXT)
