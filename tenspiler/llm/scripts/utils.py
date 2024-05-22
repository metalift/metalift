import json
import re
import subprocess
import textwrap
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Union, get_args

from metalift.frontend.llvm import Driver
from metalift.ir import (
    Bool,
    Call,
    Eq,
    Expr,
    FnDecl,
    FnDeclRecursive,
    Int,
    List,
    Lit,
    Object,
    Var,
)
from metalift.rosette_translator import generate_vars
from metalift.vc_util import and_objects
from tenspiler.constants import TENSPILER_FNS
from tenspiler.llm.analysis import (
    analyze_blend_double_loop,
    analyze_dissolve_blend_8,
    analyze_matmul,
    analyze_normal_blend_8,
    analyze_normal_blend_f,
    analyze_rmsnorm_part1,
    analyze_rmsnorm_part2,
    analyze_softmax_part1,
    analyze_softmax_part2,
    analyze_softmax_part3,
    analyze_softmax_part4,
    analyze_transformer_part1,
    analyze_transformer_part2,
    analyze_transformer_part3,
    analyze_transformer_part4,
)

TEMPLATE_SYS = "You are a helpful expert in programming languages."
TEMPLATE_ERR = "These generated programs are incorrect. Do not generate the same Please generate another program."


# regex to extract the code from the completions
def extract(s) -> list[str]:
    extracted_result = [
        x.group(1)
        for x in re.finditer(r"```(?:Python|python|assembly)?(.*?)```", s, re.DOTALL)
    ]
    if len(extracted_result) == 0:
        return [s]
    return extracted_result


# TODO(jie): add type
def extract_and_save(choices, output_file: Path) -> str:
    final_content: list[str] = []
    for choice in choices:
        if isinstance(choice, str):
            # For testing purpose
            content = choice
        else:
            content = choice.message.content
        final_content.append("\n\n".join(extract(content)))

    with open(output_file, "w") as f:
        json.dump(final_content, f)
    return final_content


# TODO(jie): add type
def get_ps_choice_and_save_prompt(
    *,
    client,
    source_code: str,
    dsl_code: str,
    output_file: Path,
    prev_incorrect_sols: set[str],
):
    # return [
    #     f"""
    #     def transformer_part2(
    #         token_position: int,
    #         head: int,
    #         head_size: int,
    #         key_cache_layer: List[List[int]],
    #         attention: List[int]
    #     ) -> List[int]:

    #         return matrix_vec_mul(
    #             matrix_transpose(
    #                 matrix_col_slice(
    #                     matrix_row_slice(key_cache_layer, 0, token_position + 1),
    #                     head * head_size,
    #                     (head + 1) * head_size
    #                 )
    #             ),
    #             attention[:token_position + 1]
    #         )
    #     """
    # ]
    # return [
    #     f"""
    #     def transformer_part4(input1: List[int], input2: List[int], hidden_dim: int) -> List[int]:
    #         return vec_elemwise_mul(vec_slice(input1, 0, hidden_dim), vec_slice(input2, 0, hidden_dim))
    #     """
    # ]
    ps_template_text = f"""
    Your task is to rewrite the given `test` C++ Function. You need to use only the set of provided functions and constants to achieve this. The rewritten program should be semantically equivalent to the `test` function.
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
    messages = [
        {"role": "system", "content": TEMPLATE_SYS},
        {"role": "user", "content": ps_template_text},
    ]
    if len(prev_incorrect_sols) > 0:
        messages.append(
            {"role": "assistant", "content": "\n\n".join(prev_incorrect_sols)}
        )
        messages.append({"role": "user", "content": TEMPLATE_ERR})

    with open(output_file, "w") as f:
        json.dump(messages, f)

    call_start_time = time.time()
    message = client.messages.create(
        model="claude-3-opus-20240229",
        max_tokens=1000,
        temperature=0.0,
        system=TEMPLATE_SYS,
        messages=[{"role": "user", "content": ps_template_text}],
    )
    # outputs = client.chat.completions.create(
    #     model="gpt-4",  # model to use
    #     messages=messages,
    #     n=50,  # We always sample 1 solution at a time
    #     temperature=0.7,
    # )
    call_end_time = time.time()
    print(f"ps call took {call_end_time - call_start_time}s")
    return [message.content[0].text]


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


blend_double_loops = DoubleLoopInfo(
    outer_loop_var=Int("row").src,
    inner_loop_var=Int("col").src,
    outer_loop_read_vars=[
        List(List[Int], "base").src,
        List(List[Int], "active").src,
    ],
    inner_loop_read_vars=[
        List(List[Int], "base").src,
        List(List[Int], "active").src,
        Int("row").src,
    ],
    outer_loop_modified_vars=[List(List[Int], "out").src],
    inner_loop_modified_vars=[List(List[Int], "out").src, List(Int, "row_vec").src],
)

_output_var_map = {
    "normal_blend_f": List(Int, "out").src,
    "normal_blend_8": List(Int, "out").src,
    "darken_blend_8": List(List[Int], "out").src,
    "multiply_blend_8": List(List[Int], "out").src,
    "linear_burn_8": List(List[Int], "out").src,
    "color_burn_8": List(List[Int], "out").src,
    "lighten_blend_8": List(List[Int], "out").src,
    "screen_blend_8": List(List[Int], "out").src,
    "linear_dodge_8": List(List[Int], "out").src,
    "color_dodge_8": List(List[Int], "out").src,
    "overlay_blend_8": List(List[Int], "out").src,
    "dissolve_blend_8": List(List[Int], "out").src,
    "softmax_part1": Int("max_val").src,
    "softmax_part2": List(Int, "output").src,
    "softmax_part3": Int("sum").src,
    "softmax_part4": List(Int, "output").src,
    "rmsnorm_part1": Int("ss").src,
    "rmsnorm_part2": List(Int, "output").src,
    "matmul": List(Int, "output").src,
    "transformer_part1": List(Int, "attention").src,
    "transformer_part2": List(Int, "xb").src,
    "transformer_part3": List(Int, "output").src,
    "transformer_part4": List(Int, "output").src,
}

_loop_info_map = {
    "normal_blend_f": SingleLoopInfo(
        loop_var=Int("i").src,
        modified_vars=[List(Int, "out").src],
        read_vars=[List(Int, "base").src, List(Int, "active").src, Int("opacity").src],
    ),
    "normal_blend_8": SingleLoopInfo(
        loop_var=Int("i").src,
        modified_vars=[List(Int, "out").src],
        read_vars=[List(Int, "base").src, List(Int, "active").src, Int("opacity").src],
    ),
    "darken_blend_8": blend_double_loops,
    "multiply_blend_8": blend_double_loops,
    "linear_burn_8": blend_double_loops,
    "color_burn_8": blend_double_loops,
    "lighten_blend_8": blend_double_loops,
    "screen_blend_8": blend_double_loops,
    "linear_dodge_8": blend_double_loops,
    "color_dodge_8": blend_double_loops,
    "overlay_blend_8": blend_double_loops,
    "dissolve_blend_8": DoubleLoopInfo(
        outer_loop_var=Int("row").src,
        inner_loop_var=Int("col").src,
        outer_loop_read_vars=[
            List(List[Int], "base").src,
            List(List[Int], "active").src,
            Int("opacity").src,
            Int("rand_cons").src,
        ],
        inner_loop_read_vars=[
            List(List[Int], "base").src,
            List(List[Int], "active").src,
            Int("opacity").src,
            Int("rand_cons").src,
            Int("row").src,
        ],
        outer_loop_modified_vars=[List(List[Int], "out").src],
        inner_loop_modified_vars=[List(List[Int], "out").src, List(Int, "row_vec").src],
    ),
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
        modified_vars=[List(Int, "output").src],
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
        outer_loop_modified_vars=[List(Int, "output").src],
        inner_loop_modified_vars=[List(Int, "output").src, Int("curr").src],
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
        outer_loop_modified_vars=[List(Int, "attention").src],
        inner_loop_modified_vars=[List(Int, "attention").src, Int("score").src],
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
        outer_loop_modified_vars=[List(Int, "xb").src],
        inner_loop_modified_vars=[List(Int, "xb").src, Int("curr").src],
    ),
    "transformer_part3": SingleLoopInfo(
        loop_var=Int("i").src,
        read_vars=[List(Int, "input").src, Int("hidden_dim").src],
        modified_vars=[List(Int, "output").src],
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


def _generate_invariant_template(benchmark_name: str) -> str:
    loop_info = _loop_info_map[benchmark_name]
    if isinstance(loop_info, SingleLoopInfo):
        arguments = get_args_for_invariants(benchmark_name)
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
        outer_inv_args, inner_inv_args = get_args_for_invariants(benchmark_name)
        outer_inv_args_with_types = ", ".join(
            [
                f"{arg}: {arg.type.to_python_type_str(get_args(arg.type))}"
                for arg in outer_inv_args
            ]
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


def get_inv_choice_and_save_prompt(
    *,
    client,
    benchmark_name: str,
    ps_solution: str,
    source_code: str,
    dsl_code: str,
    output_file: Path,
    prev_incorrect_sols: set[str],
):
    # return [
    #     f"""
    #     def invariant(i: int, hidden_dim: int, input: List[int], output: List[int]) -> bool:
    #         return i >= 0 and i <= hidden_dim and output == vec_elemwise_mul(input[:i], vec_map(input[:i], lambda x: 1 // (1 + integer_exp(0 - x))))
    #     """
    # ]
    # prompt for generating invariants of a function.
    inv_template_text = f"""Your task is to prove that `assertion` is true in the `test` function. The assertion can proved by finding a loop invariant using the defined functions. Write the loop invariant as a python boolean formula.

    #Instructions:
    1. You need to use only the defined functions to write the loop invariant.
    2. Do not use for/while loops for rewriting the function.
    3. The rewritten program should just be a single return statement of the form return_var = provided_function(...)
    4. Inline all the expressions. Do not use intermediate variables.
    5. Generate separate loop invariants for each loop in the test function.
    6. invariant structure
    ```
    {_generate_invariant_template(benchmark_name)}
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
        assert out == matrix_elemwise_sub(base, active);
    }}
    def invariant1(row, col, base, active, out):
        return row >= 0 and row <= base.size() and out == matrix_elemwise_sub(base[:row], active[:row])
    def invariant2(row, col, base, active, row_vec, out):
        return row >= 0 and row < base.size() and col >= 0 and col <= base[0].size() and row_vec == vec_elemwise_sub(base[row][:col], active[row][:col]) and out == matrix_elemwise_sub(base[:row], active[:row])
    ```

    Example2:
    ```
    #defined functions
    {dsl_code}

    //test function
    {_get_inv_source_code(ps_solution, source_code)}
    ```
    """
    messages = [
        {"role": "system", "content": TEMPLATE_SYS},
        {"role": "user", "content": inv_template_text},
    ]
    if len(prev_incorrect_sols) > 0:
        messages.append(
            {"role": "assistant", "content": "\n\n".join(prev_incorrect_sols)}
        )
        messages.append({"role": "user", "content": TEMPLATE_ERR})

    with open(output_file, "w") as f:
        json.dump(messages, f)

    call_start_time = time.time()
    message = client.messages.create(
        model="claude-3-opus-20240229",
        max_tokens=1000,
        temperature=0.0,
        system=TEMPLATE_SYS,
        messages=[{"role": "user", "content": inv_template_text}],
    )
    # outputs = client.chat.completions.create(
    #     model="gpt-4",  # model to use
    #     messages=messages,
    #     n=50,
    #     temperature=0.7,
    # )
    call_end_time = time.time()
    print(f"inv call took {call_end_time - call_start_time}s")
    return [message.content[0].text]


def replace_in_call(expr: Expr, in_call: tuple[str, str]) -> Expr:
    caller_fn_name, callee_fn_name = in_call
    if (
        isinstance(expr, Call)
        or isinstance(expr, FnDecl)
        or isinstance(expr, FnDeclRecursive)
    ):
        new_args = []
        for arg in expr.arguments():
            if isinstance(arg, FnDecl) or isinstance(arg, FnDeclRecursive):
                if arg.name() == callee_fn_name and expr.name() == caller_fn_name:
                    new_args.append(Var(callee_fn_name, arg.type))
                else:
                    new_args.append(replace_in_call(arg, in_call))
            else:
                new_args.append(replace_in_call(arg, in_call))
        if isinstance(expr, Call):
            return Call(expr.name(), expr.type, *new_args)
        elif isinstance(expr, FnDecl):
            return FnDecl(
                expr.name(),
                expr.returnT(),
                replace_in_call(expr.body(), in_call),
                *new_args,
            )
        else:
            return FnDeclRecursive(
                expr.name(),
                expr.returnT(),
                replace_in_call(expr.body(), in_call),
                *new_args,
            )
    elif isinstance(expr, Var) or isinstance(expr, Lit):
        return expr
    else:
        return expr.map_args(lambda x: replace_in_call(x, in_call))


def replace_in_calls(expr: Expr, in_calls: list[tuple[str, str]]) -> Expr:
    for in_call in in_calls:
        expr = replace_in_call(expr, in_call)
    return expr


def get_args_for_invariants(
    benchmark_name: str,
) -> Union[list[Object], tuple[list[Object], list[Object]]]:
    loop_info = _loop_info_map[benchmark_name]
    if isinstance(loop_info, SingleLoopInfo):
        return sorted(
            list(
                set(
                    loop_info.read_vars + loop_info.modified_vars + [loop_info.loop_var]
                )
            ),
            key=lambda x: x.name(),
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
        return outer_inv_args, inner_inv_args


def process_ps_fn_decl(
    fn_decl: Union[FnDecl, FnDeclRecursive],
    output_var: Object,
) -> Union[FnDecl, FnDeclRecursive]:
    return fn_decl.__class__(
        f"{fn_decl.name()}_ps",
        Bool,
        Eq(output_var, fn_decl.body()),
        *fn_decl.arguments(),
        output_var,
    )


def analyze_benchmark(benchmark_name: str) -> Driver:
    print(f"Analyzing benchmark {benchmark_name}")
    driver = Driver()
    inv_args = get_args_for_invariants(benchmark_name)
    if benchmark_name in {
        "darken_blend_8",
        "multiply_blend_8",
        "linear_burn_8",
        "color_burn_8",
        "lighten_blend_8",
        "screen_blend_8",
        "linear_dodge_8",
        "color_dodge_8",
        "overlay_blend_8",
    }:
        analyze_blend_double_loop(driver, benchmark_name, inv_args)
    elif benchmark_name == "dissolve_blend_8":
        analyze_dissolve_blend_8(driver, inv_args)
    elif benchmark_name == "normal_blend_f":
        analyze_normal_blend_f(driver, inv_args)
    elif benchmark_name == "normal_blend_8":
        analyze_normal_blend_8(driver, inv_args)
    elif benchmark_name == "softmax_part1":
        analyze_softmax_part1(driver, inv_args)
    elif benchmark_name == "softmax_part2":
        analyze_softmax_part2(driver, inv_args)
    elif benchmark_name == "softmax_part3":
        analyze_softmax_part3(driver, inv_args)
    elif benchmark_name == "softmax_part4":
        analyze_softmax_part4(driver, inv_args)
    elif benchmark_name == "rmsnorm_part1":
        analyze_rmsnorm_part1(driver, inv_args)
    elif benchmark_name == "rmsnorm_part2":
        analyze_rmsnorm_part2(driver, inv_args)
    elif benchmark_name == "matmul":
        analyze_matmul(driver, inv_args)
    elif benchmark_name == "transformer_part1":
        analyze_transformer_part1(driver, inv_args)
    elif benchmark_name == "transformer_part2":
        analyze_transformer_part2(driver, inv_args)
    elif benchmark_name == "transformer_part3":
        analyze_transformer_part3(driver, inv_args)
    elif benchmark_name == "transformer_part4":
        analyze_transformer_part4(driver, inv_args)
    else:
        raise ValueError(f"Unknown benchmark: {benchmark_name}")
    return driver


def get_inv_and_ps(
    *,
    client,
    benchmark_name: str,
    source_code: str,
    dsl_code: str,
    output_file: Path,
    prev_incorrect_sols: set[str],
):
    inv_ps_template_text = f"""Your task is to rewrite the given `test` C++ Function. You need to use only the set of provided functions and constants to achieve this. The rewritten program should be semantically equivalent to the `test` function. In addition, your task is to prove that rewritten function is equivalent to the `test` function. We can prove this by finding a loop invariant using the defined functions. Write the loop invariant as a python boolean formula.
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
    {_generate_invariant_template(benchmark_name)}
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
    messages = [
        {"role": "system", "content": TEMPLATE_SYS},
        {"role": "user", "content": inv_ps_template_text},
    ]
    if len(prev_incorrect_sols) > 0:
        messages.append(
            {"role": "assistant", "content": "\n\n".join(prev_incorrect_sols)}
        )
        messages.append({"role": "user", "content": TEMPLATE_ERR})

    with open(output_file, "w") as f:
        json.dump(messages, f)

    call_start_time = time.time()
    outputs = client.chat.completions.create(
        model="gpt-4",  # model to use
        messages=messages,
        n=10,
        temperature=0.7,
    )
    call_end_time = time.time()
    print(f"inv ps call took {call_end_time - call_start_time}s")
    return outputs.choices, call_end_time - call_start_time


def verify_benchmark(
    *,
    driver: Driver,
    benchmark_name: str,
    synthesized_fn_decls: list[Union[FnDecl, FnDeclRecursive]],
    in_calls: list[tuple[str, str]],
    list_bound: int = 2,
    bitwidth: int = 6,
) -> bool:
    print(f"Generating verification file for benchmark {benchmark_name}")

    synthesis_logs_dir = Path("./synthesisLogs")
    synthesis_logs_dir.mkdir(exist_ok=True)
    verify_file_name = f"./synthesisLogs/verify_{benchmark_name}.rkt"
    f = open(verify_file_name, "w")
    print(
        "#lang rosette\n"
        + '(require "./bounded.rkt")\n'
        + '(require "./utils.rkt")\n'
        + "(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)\n"
        + "(require rosette/solver/smt/bitwuzla)\n"
        + '(current-solver (bitwuzla #:path "/Users/jieq/Desktop/bitwuzla/build/src/main/bitwuzla" #:options (hash \':seed 0)))\n'
        + "\n",
        # + "(require rosette/solver/smt/z3)\n"
        # + "(current-solver (z3 #:options (hash ':random-seed 0)))\n"
        # + "\n",
        file=f,
    )
    # write dsl code
    for fn_decl in TENSPILER_FNS:
        # Skip some functions that are already in utils.rkt
        # TODO(jie): this is a bit hacky. We could remove all these functions in utils.rkt, but then we need to make sure that they are added to perspective driver files.
        if fn_decl.name().startswith("integer"):
            continue
        if fn_decl.name() in {"firsts"}:
            continue
        if fn_decl.body() is None:
            continue

        fn_decl = replace_in_calls(fn_decl, in_calls)
        print("\n", fn_decl.to_rosette(), "\n", file=f)

    # write ps and inv
    for fn_decl in synthesized_fn_decls:
        # Change function names
        # Change single loop invariant names
        if fn_decl.name() == "invariant":
            fn_decl.set_name(f"{benchmark_name}_inv0")

        # Change double loop invariant names
        if fn_decl.name() == "invariant1":
            fn_decl.set_name(f"{benchmark_name}_inv0")
        if fn_decl.name() == "invariant2":
            fn_decl.set_name(f"{benchmark_name}_inv1")

        # Change ps function name
        if fn_decl.name() == benchmark_name:
            fn_decl = process_ps_fn_decl(fn_decl, _output_var_map[benchmark_name])
        print("\n", replace_in_calls(fn_decl, in_calls).to_rosette(), "\n", file=f)

    # Write variables
    vars = set(driver.var_tracker.all())
    var_decls, _ = generate_vars(vars, list_bound)
    print(var_decls, file=f)

    # Write bitwidth
    print(f"(current-bitwidth {bitwidth})", file=f)

    # Write assertions
    vc = and_objects(*driver.asserts).src.simplify()
    vc = replace_in_calls(vc, in_calls)

    print(f"(define vc (verify (assert {vc.to_rosette()})))\n", file=f)
    print("vc", file=f)

    f.close()

    # Run the verification
    print(f"Running verification for benchmark {benchmark_name}")
    return False
    verification_output = subprocess.run(
        ["racket", verify_file_name], check=True, capture_output=True
    )
    if verification_output.stdout.decode("utf-8").split("\n")[0] == "(unsat)":
        print("Verification successful")
        print("\n\n")
        return True
    else:
        print("Verification failed")
        print(verification_output.stdout.decode("utf-8"))
        print("\n\n")
        return False
