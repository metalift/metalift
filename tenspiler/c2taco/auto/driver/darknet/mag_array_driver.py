from tenspiler.axioms import reduce_sum_axiom, vec_elemwise_mul_axiom
from tenspiler.codegen.utils import DataType
from tenspiler.tree_parser import analyze_single_loop
from tenspiler.utils.synthesis_utils import run_synthesis_algorithm

if __name__ == "__main__":
    driver, input_vars, mag_array = analyze_single_loop(
        file_path="tenspiler/c2taco/cpp/for_synthesis/darknet/mag_array.cc",
        func_name="mag_array",
        axioms=[reduce_sum_axiom, vec_elemwise_mul_axiom],
    )
    a, n = input_vars["a"], input_vars["n"]
    driver.add_precondition(n >= 1)
    driver.add_precondition(a.len() > 0)
    driver.add_precondition(a.len() >= n)
    mag_array(a, n)
    run_synthesis_algorithm(
        driver=driver,
        data_type=DataType.INT32,
        benchmark_name="mag_array",
        has_relaxed=False,
    )
