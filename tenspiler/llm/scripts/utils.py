import json
import re
import textwrap
from dataclasses import dataclass
from typing import Union, get_args

from metalift.frontend.llvm import Driver
from metalift.ir import FnDecl, FnDeclRecursive, Int, List, Var
from metalift.rosette_translator import generate_vars
from metalift.vc_util import and_objects
from tenspiler.constants import TENSPILER_FNS
from tenspiler.llm.analysis import analyze_darken_blend_8

TEMPLATE_SYS = "You are a helpful expert in programming languages."


# regex to extract the code from the completions
def extract(s):
    return [
        x.group(1)
        for x in re.finditer(r"```(?:Python|python|assembly)?(.*?)```", s, re.DOTALL)
    ]


# TODO(jie): add type
def extract_and_write(choices, output_file) -> list[str]:
    responses: list[str] = []
    for i, choice in enumerate(choices):
        extracted_output = "\n\n".join(extract(choice.message.content))
        responses.append(extracted_output)

    with open(output_file, "w") as f:
        json.dump(responses, f)
    return responses


# TODO(jie): add type
def get_ps_choices(*, client, source_code: str, dsl_code: str, n_choices: int):
    # prompt for guessing the post conditions of a function. dsl_code is the set of functions and constants that can be used to rewrite the function. source_code is the function to be rewritten.
    ps_template_text = f"""
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
    # call the completions endpoint to get the completions for the prompt
    outputs = client.chat.completions.create(
        model="gpt-4",  # model to use
        messages=[
            {"role": "system", "content": TEMPLATE_SYS},
            {"role": "user", "content": ps_template_text},
        ],
        n=n_choices,  # number of candidates,
        temperature=0.7,
    )
    return outputs.choices


######
# Some helper classes and functions for inv
######
@dataclass
class SingleLoopInfo:
    loop_var: Var
    read_vars: list[Var]
    modified_vars: list[Var]


@dataclass
class DoubleLoopInfo:
    outer_loop_var: Var
    inner_loop_var: Var
    outer_loop_read_vars: list[Var]
    inner_loop_read_vars: list[Var]
    outer_loop_modified_vars: list[Var]
    inner_loop_modified_vars: list[Var]


_loop_info_map = {
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


def get_num_inv_funcs(benchmark_name: str) -> int:
    if isinstance(_loop_info_map[benchmark_name], SingleLoopInfo):
        return 1
    elif isinstance(_loop_info_map[benchmark_name], DoubleLoopInfo):
        return 2
    else:
        raise ValueError(f"Invalid loop info for {benchmark_name}")


def _generate_invariant_template(
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


def _get_ps_expr(ps_solution: str) -> str:
    extracted_ps_solution = extract(ps_solution)
    if len(extracted_ps_solution) == 1:
        extracted_ps_solution = extracted_ps_solution[0]
    elif len(extracted_ps_solution) == 0:
        extracted_ps_solution = ps_solution
    else:
        raise ValueError("More than one code block extracted from the ps code")
    expr = extracted_ps_solution.split("return")[1].replace("\n", "").strip()
    expr = re.sub(r"\s+", " ", expr)
    return expr


def _get_inv_source_code(ps_code: str, source_code: str) -> str:
    # Extract the 1 line post condition from the ps_code
    ps_expr = _get_ps_expr(ps_code)
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
            lines[idx] = f"assert {return_var} == {ps_expr}"
            break
    return "\n".join(lines)


def get_inv_choices(
    *,
    client,
    benchmark_name: str,
    ps_solution: str,
    source_code: str,
    dsl_code: str,
    n_choices: int,
):
    # prompt for generating invariants of a function.
    inv_template_text = f"""Your task is to prove that `assertion` is true in the `test` function. The assertion can proved by finding a loop invariant using the defined functions. Write the loop invariant as a python boolean formula. Please do not generate any explanations.

    #Instructions:
    1. You need to use only the defined functions to write the loop invariant.
    2. Do not use for/while loops for rewriting the function.
    3. The rewritten program should just be a single return statement of the form return_var = provided_function(...)
    4. Inline all the expressions. Do not use intermediate variables.
    5. Generate separate loop invariants for each loop in the test function.
    6. invariant structure
    ```
    {_generate_invariant_template(_loop_info_map[benchmark_name])}
    ```

    Example1:
    ```
    #defined functions
    def map(data: list[int] , f: func):
        return [f(x) for x in data]
    def reduce(data: list[int] , f: func):
        if len(data) == 0:
            return 0
        else:
            return f(data[0], reduce(data[1:], f))
    def add(a: int , b: int):
        return a + b
    constants = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
    #test function
    def test(data: list[int]):
        count = 0
        for i in range(len(data)):
            count += 1
        assert count == reduce(map(data, lambda x: 1), add)
    def invariant(data: list[int], count: int, i:int):
        return i >= 0 and i <= len(data) and count == reduce(map(data[:i], lambda x: 1), add)
    ```

    Example2:
    ```
    #defined functions
    {dsl_code}

    //test function
    {_get_inv_source_code(ps_solution, source_code)}
    ```
    """
    outputs = client.chat.completions.create(
        model="gpt-4",  # model to use
        messages=[
            {"role": "system", "content": TEMPLATE_SYS},
            {"role": "user", "content": inv_template_text},
            # {"role": "assistant", "content": sol},
            # {"role": "user", "content": "This invariant is incorrect, generate another one."}
        ],
        n=n_choices,  # number of candidates,
        temperature=0.7,
    )
    return outputs.choices


def verify_benchmark(
    *,
    benchmark_name: str,
    synthesized_fn_decls: list[Union[FnDecl, FnDeclRecursive]],
    list_bound: int = 2,
    bitwidth: int = 6,
) -> None:
    driver = Driver()

    if benchmark_name == "darken_blend_8":
        analyze_darken_blend_8(driver)
    else:
        raise ValueError(f"Unknown benchmark: {benchmark_name}")

    f = open(f"./synthesisLogs/verify_{benchmark_name}.rkt", "w")
    print(
        "#lang rosette\n"
        + '(require "./bounded.rkt")\n'
        + '(require "./utils.rkt")\n'
        + "(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)\n"
        + "(require rosette/solver/smt/bitwuzla)\n"
        + '(current-solver (bitwuzla #:path "/home/c/Desktop/research/ml/bitwuzla/build/src/main/bitwuzla" #:options (hash \':seed 0)))\n'
        + "\n",
        # + "(require rosette/solver/smt/z3)\n"
        # + "(current-solver (z3 #:options (hash ':random-seed 0)))\n"
        # + "\n",
        file=f,
    )
    # write dsl code
    for fn_decl in TENSPILER_FNS:
        print("\n", fn_decl.to_rosette(), "\n", file=f)

    # write ps and inv
    for fn_decl in synthesized_fn_decls:
        print("\n", fn_decl.to_rosette(), "\n", file=f)

    # Write variables
    vars = set(driver.var_tracker.all())
    var_decls, _ = generate_vars(vars, list_bound)
    print(var_decls, file=f)

    # Write bitwidth
    print(f"(current-bitwidth {bitwidth})", file=f)

    # Write assertions
    vc = and_objects(*driver.asserts).src.simplify()
    print("(define (assertions)\n (assert %s))\n" % vc.to_rosette(), file=f)
    print("(verify (assertions))", file=f)

    f.close()

    # TODO(jie): add step to run
