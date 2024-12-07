from metalift.frontend.llvm import Driver
from tenspiler.axioms import matrix_scalar_mul_axiom, vec_scalar_mul_axiom
from tenspiler.codegen.utils import DataType
from tenspiler.tree_parser import analyze_double_loops
from tenspiler.utils.synthesis_utils import run_synthesis_algorithm

if __name__ == "__main__":
    driver = Driver()
    driver, input_vars, scale_matrix = analyze_double_loops(
        file_path="tenspiler/c2taco/cpp/for_synthesis/darknet/scale_matrix.cc",
        func_name="scale_matrix",
        axioms=[vec_scalar_mul_axiom, matrix_scalar_mul_axiom],
    )
    m, scale = input_vars["m"], input_vars["scale"]

    # Add preconditions
    driver.add_precondition(m.len() >= 1)
    driver.add_precondition(m[0].len() >= 1)

    scale_matrix(m, scale)
    run_synthesis_algorithm(
        driver=driver,
        data_type=DataType.INT32,
        benchmark_name="scale_matrix",
        has_relaxed=False,
    )
