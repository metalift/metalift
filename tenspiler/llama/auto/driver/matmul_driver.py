from metalift.frontend.llvm import Driver
from tenspiler.axioms import (
    matrix_vec_mul_axiom,
    reduce_sum_axiom,
    vec_scalar_mul_axiom,
)
from tenspiler.codegen.utils import DataType
from tenspiler.tree_parser import analyze_double_loops
from tenspiler.utils.synthesis_utils import run_synthesis_algorithm

if __name__ == "__main__":
    driver = Driver()
    driver, input_vars, matmul = analyze_double_loops(
        file_path="tenspiler/llama/cpp/for_synthesis/matmul.cc",
        func_name="matmul",
        axioms=[
            vec_scalar_mul_axiom,
            reduce_sum_axiom,
            matrix_vec_mul_axiom,
        ],
    )
    weight, input = input_vars["weight"], input_vars["input"]
    driver.add_precondition(weight.len() > 0)
    driver.add_precondition(weight[0].len() > 0)
    driver.add_precondition(weight[0].len() == input.len())
    matmul(weight, input)
    run_synthesis_algorithm(
        driver=driver,
        data_type=DataType.UINT_8,
        benchmark_name="matmul",
        has_relaxed=False,
    )
