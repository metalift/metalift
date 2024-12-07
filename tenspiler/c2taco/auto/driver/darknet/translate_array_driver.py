from tenspiler.axioms import vec_scalar_add_axiom
from tenspiler.codegen.utils import DataType
from tenspiler.tree_parser import analyze_single_loop
from tenspiler.utils.synthesis_utils import run_synthesis_algorithm

if __name__ == "__main__":
    driver, input_vars, translate_array = analyze_single_loop(
        file_path="tenspiler/c2taco/cpp/for_synthesis/darknet/translate_array.cc",
        func_name="translate_array",
        axioms=[vec_scalar_add_axiom],
    )
    a, n, s = input_vars["a"], input_vars["n"], input_vars["s"]
    driver.add_precondition(n >= 1)
    driver.add_precondition(a.len() >= n)
    translate_array(a, n, s)
    run_synthesis_algorithm(
        driver=driver,
        data_type=DataType.INT32,
        benchmark_name="translate_array",
        has_relaxed=False,
    )
