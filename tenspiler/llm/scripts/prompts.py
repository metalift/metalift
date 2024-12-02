from tenspiler.llm.scripts.utils import (
    _generate_invariant_template,
    _loop_info_map,
    is_single_loop,
)


def get_ps_prompt(*, dsl_code: str, source_code: str) -> str:
    ps_text = f"""
    Your task is to rewrite the given `test` C++ Function. You need to use only the set of provided functions and constants to achieve this. The rewritten program should be semantically equivalent to the `test` function. Please generate the shortest possible solution.

    #Instructions
    # 1. Do not use for/while loops for rewriting the function.
    # 2. The rewritten program should just be a single return statement of the form return provided_function(...)
    # 3. Inline all the expressions. Do not use intermediate variables. Return the function signature as well as the function body in python.

    #defined functions
    ```python
    {dsl_code}
    ```

    ```cpp
    //test function
    {source_code}
    ```
    """
    return ps_text


def get_inv(suite_name: str, benchmark_name: str, dsl_code: str) -> None:
    # TODO(jie): move this to utils
    with open(f"tenspiler/llm/inv_code/{suite_name}/{benchmark_name}.txt") as f:
        inv_code_with_assert = f.read()
    if is_single_loop(benchmark_name):
        single_loop_info = _loop_info_map[benchmark_name]
        loop_var_name = single_loop_info.loop_var.name()
        single_loop_inv_text = f"""
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
        # 1. It should have boolean expressions over the loop index variable `{loop_var_name}` to describe the valid range of `{loop_var_name}`.
        # 2. It should have an inductive expression describing the output variable `out` using the defined functions.
        {_generate_invariant_template(benchmark_name)}
        ```
        """
        # single_loop_one_shot_inv_text = f"""
        # Your task is to prove that `assertion` is true in the `test` function. The assertion can be proved by finding a loop invariant using the defined functions. Write the loop invariant as a python boolean formula.

        # #Instructions:
        # 1. You need to use only the defined functions to write the loop invariant.
        # 2. Do not use for/while loops for rewriting the function.
        # 3. The rewritten program should just be a single return statement of the form return\_var = provided\_function(...)
        # 4. Inline all the expressions. Do not use intermediate variables.
        # 5. Generate separate loop invariants for each loop in the test function.
        # 6. invariant structure
        # {_generate_invariant_template(benchmark_name)}

        # Example1:
        # #defined functions
        # {dsl_code}

        # //test function
        # vector<vector<uint8_t>> test(vector<vector<uint8_t>> base, vector<vector<uint8_t>> active) {{
        #     vector<vector<uint8_t>> out;
        #     uint8_t m = base.size();
        #     uint8_t n = base[0].size();
        #     for (uint8_t row = 0; row < m; row++) {{
        #         vector<uint8_t> row_vec;
        #         for (uint8_t col = 0; col < n; col++) {{
        #             uint8_t pixel = base[row][col] - active[row][col] ;
        #             row_vec.push_back(pixel);
        #         }}
        #         out.push_back(row_vec);
        #     }}
        #     assert out == matrix_elemwise_sub(base, active);
        # }}
        # def invariant1(row, col, base, active, out):
        #     return row >= 0 and row <= base.size() and out == matrix_elemwise_sub(base[:row], active[:row])

        # def invariant2(row, col, base, active, row_vec, out):
        # return row >= 0 and row < base.size() and col >= 0 and col <= base[0].size() and
        #     row_vec == vec_elemwise_sub(base[row][:col], active[row][:col]) and
        #     out == matrix_elemwise_sub(base[:row], active[:row])

        # Example2:
        # {inv_code_with_assert}
        # """
        return single_loop_inv_text
    else:
        double_loop_info = _loop_info_map[benchmark_name]
        outer_loop_var = double_loop_info.outer_loop_var.name()
        inner_loop_var = double_loop_info.inner_loop_var.name()
        outer_loop_modified_vars = double_loop_info.outer_loop_modified_vars
        assert len(outer_loop_modified_vars) == 1
        inner_modified_vars_not_in_outer = [
            var
            for var in double_loop_info.inner_loop_modified_vars
            if var not in outer_loop_modified_vars
        ]
        assert len(inner_modified_vars_not_in_outer) == 1
        inner_modified_var = inner_modified_vars_not_in_outer[0].name()

        rv_var = outer_loop_modified_vars[0].name()
        outer_inv, inner_inv = _generate_invariant_template(benchmark_name)
        double_loop_inv_text = f"""
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
        return double_loop_inv_text
