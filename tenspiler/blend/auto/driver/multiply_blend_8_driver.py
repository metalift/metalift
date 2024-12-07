from metalift.frontend.llvm import Driver
from tenspiler.axioms import matrix_elemwise_mul_axiom, matrix_scalar_div_axiom
from tenspiler.codegen.utils import DataType
from tenspiler.tree_parser import analyze_double_loops
from tenspiler.utils.synthesis_utils import run_synthesis_algorithm

if __name__ == "__main__":
    driver = Driver()
    driver, input_vars, multiply_blend_8 = analyze_double_loops(
        file_path="tenspiler/blend/cpp/for_synthesis/multiply_blend_8.cc",
        func_name="multiply_blend_8",
        axioms=[matrix_scalar_div_axiom, matrix_elemwise_mul_axiom],
    )
    base, active = input_vars["base"], input_vars["active"]
    driver.add_precondition(base.len() > 1)
    driver.add_precondition(base.len() == active.len())
    driver.add_precondition(base[0].len() == active[0].len())
    multiply_blend_8(base, active)
    run_synthesis_algorithm(
        driver=driver,
        data_type=DataType.UINT_8,
        benchmark_name="multiply_blend_8",
        has_relaxed=False,
    )
