import re
import textwrap
from typing import Optional, get_args

from llm.utils import NestedLoopInfo, SequentialLoopInfo, SingleLoopInfo, get_inv_args
from metalift.ir import FnDecl, FnDeclRecursive


def generate_invariant_template(
    loop_info: SingleLoopInfo | NestedLoopInfo | SequentialLoopInfo,
) -> list[str]:
    """Given the loop information, generate the invariant template."""

    def _generate_invariant_template_single_loop(
        loop_info: SingleLoopInfo, index: Optional[int] = None
    ) -> str:
        arguments = get_inv_args(loop_info)
        args_with_types = ", ".join(
            [
                f"{arg}: {arg.type.to_python_type_str(get_args(arg.type))}"
                for arg in arguments
            ]
        )
        loop_var = loop_info.loop_var.src.name()
        modified_vars_cond = " and ".join(
            [
                f"{var} == operation over defined functions"
                for var in loop_info.modified_vars
            ]
        )
        return textwrap.dedent(
            f"""
            def invariant{f'{index}' if index is not None else ''}({args_with_types}) -> bool:
                return expression over loop index variable {loop_var} and {modified_vars_cond}
            """
        )

    if isinstance(loop_info, SingleLoopInfo):
        return _generate_invariant_template_single_loop(loop_info)
    elif isinstance(loop_info, NestedLoopInfo):
        outer_inv_args, inner_inv_args = get_inv_args(loop_info)
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
        outer_loop_var = loop_info.outer_loop_var.src.name()
        inner_loop_var = loop_info.inner_loop_var.src.name()
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
        inv1_template = f"""
        def invariant1({outer_inv_args_with_types}) -> bool:
            return expression over loop index variable `{outer_loop_var}` and {outer_modified_vars_cond}
        """
        inv2_template = f"""
        def invariant2({inner_inv_args_with_types}) -> bool:
            return expression over loop index variable `{outer_loop_var}` and `{inner_loop_var}` and {inner_modified_vars_cond}
        """
        return [textwrap.dedent(inv1_template), textwrap.dedent(inv2_template)]
    else:
        templates: list[str] = []
        for idx, single_info in enumerate(loop_info.loop_infos):
            invariant_template = _generate_invariant_template_single_loop(
                single_info, idx + 1
            )
            templates.append(invariant_template)
        return templates


def get_ps_prompt(*, benchmark_name: str, dsl_code: str, source_code: str) -> str:
    ps_text = f"""
    Your task is to rewrite the given `{benchmark_name}` C++ Function. You need to use only the set of provided functions and constants to achieve this. The rewritten program should be semantically equivalent to the `{benchmark_name}` function. Please generate the shortest possible solution.

    #Instructions
    # 1. Do not use for/while loops for rewriting the function.
    # 2. The rewritten program should just be a single return statement of the form return provided_function(...)
    # 3. Inline all the expressions. Do not use intermediate variables. Return the function signature as well as the function body in python.
    # 4. Include full type annotations in the function signature (argument and return types).

    #defined functions
    ```python
    {dsl_code}
    ```

    ```cpp
    //{benchmark_name} function
    {source_code}
    ```
    """
    return ps_text


def get_inv_prompt(
    *,
    benchmark_name: str,
    source_code: str,
    ps_fn_decl: FnDecl | FnDeclRecursive,
    loop_info: SingleLoopInfo | NestedLoopInfo | SequentialLoopInfo,
    dsl_code: str,
    num_shots: int = 1,
) -> str:
    assertion_code = ps_fn_decl.body().to_python()
    inv_code_with_assert = re.sub(
        r"\breturn\b.*?;", rf"assert {assertion_code};", source_code
    )

    one_shot_example = f"""
    //test function
    vector<vector<uint8_t>> test(vector<vector<uint8_t>> base, vector<vector<uint8_t>> active) {{
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
    return row >= 0 and row < base.size() and col >= 0 and col <= base[0].size() and
        row_vec == vec_elemwise_sub(base[row][:col], active[row][:col]) and
        out == matrix_elemwise_sub(base[:row], active[:row])
    """
    one_shot_example = textwrap.dedent(one_shot_example)
    invariant_templates = "\n".join(generate_invariant_template(loop_info))
    one_shot_text = f"""
    Your task is to prove that `assertion` is true in the `{benchmark_name}` function. The assertion can be proved by finding a loop invariant using the defined functions. Write the loop invariant as a python boolean formula.

    #Instructions:
    1. You need to use only the defined functions to write the loop invariant.
    2. Do not use for/while loops for rewriting the function.
    3. The rewritten program should just be a single return statement of the form return\_var = provided\_function(...)
    4. Inline all the expressions. Do not use intermediate variables.
    5. Generate separate loop invariants for each loop in the {benchmark_name} function.
    6. DO NOT make any changes to the function signatures as they are used for verification downstream.
    7. invariant structure
    {invariant_templates}

    Example1:
    #defined functions
    {dsl_code}
    {one_shot_example}

    Example2:
    {inv_code_with_assert}
    """
    if isinstance(loop_info, SingleLoopInfo) or isinstance(
        loop_info, SequentialLoopInfo
    ):
        if num_shots == 0:
            if isinstance(loop_info, SingleLoopInfo):
                loop_var_names = [loop_info.loop_var.src.name()]
            else:
                loop_var_names = [
                    info.loop_var.src.name() for info in loop_info.loop_infos
                ]
            invariant_templates = "\n".join(generate_invariant_template(loop_info))
            single_loop_zero_shot_inv_text = f"""
            Your task is to generate the loop invariant `Inv` such that it is true at all the locations it is defined at.  Generate only a single `Inv` expression which holds at all the locations. The invariant needs to be generated using only the functions defined below. Write the loop invariant as a python boolean formula.
            #Instructions:
            1. You can use the defined functions to write the loop invariant. Do not use any for loops or any other python construct.
            2. Generate separate loop invariants for each loop in the test function. Return the loop invariant as a single boolean expression. Only return the invariant and no other code in a code block.
            3. Do not define intermediate variables. Inline all expressions.
            Example1:

            {dsl_code}

            //test function
            {inv_code_with_assert}

            ```
            Use the following template to generate the loop invariant
            ```

            # A strong loop invariant should have the following properties:
            # 1. It should have boolean expressions over the loop index variable(s) `{', '.join(loop_var_names)}` to describe the valid range of `{', '.join(loop_var_names)}`.
            # 2. It should have an inductive expression describing the output variable `out` using the defined functions.
            {invariant_templates}
            ```
            """
            return textwrap.dedent(single_loop_zero_shot_inv_text)
        elif num_shots == 1:
            return textwrap.dedent(one_shot_text)
        else:
            raise ValueError(
                f"Invalid number of shots for invariant prompt: {num_shots}"
            )
    elif isinstance(loop_info, NestedLoopInfo):
        outer_loop_var = loop_info.outer_loop_var.src.name()
        inner_loop_var = loop_info.inner_loop_var.src.name()
        inner_loop_modified_vars = [
            var.src for var in loop_info.inner_loop_modified_vars
        ]
        outer_loop_modified_vars = [
            var.src for var in loop_info.outer_loop_modified_vars
        ]
        assert len(outer_loop_modified_vars) == 1
        inner_modified_vars_not_in_outer = [
            var
            for var in inner_loop_modified_vars
            if var not in outer_loop_modified_vars
        ]
        assert len(inner_modified_vars_not_in_outer) == 1
        inner_modified_var = inner_modified_vars_not_in_outer[0].name()

        rv_var = outer_loop_modified_vars[0].name()
        outer_inv, inner_inv = generate_invariant_template(loop_info)
        if num_shots == 0:
            nested_loop_zero_shot_inv_text = f"""
            Your task is to generate two loop invariants `invariant1` and `invariant2` such that the given assertion holds. The invariants need to be generated using only the functions defined below. Write the loop invariants as python boolean formulas.

            #Instructions:
            1. You can use the defined functions to write the loop invariant. Do not use any for loops or any other python construct such as list comprehensions or the `all` function.
            2. Generate separate loop invariants for each loop in the test function. Return the loop invariant as a single boolean expression. Only return the invariant and no other code.
            3. Do not define intermediate variables. Inline all expressions.

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
            return textwrap.dedent(nested_loop_zero_shot_inv_text)
        elif num_shots == 1:
            return textwrap.dedent(one_shot_text)
        else:
            raise ValueError(
                f"Invalid number of shots for invariant prompt: {num_shots}"
            )
