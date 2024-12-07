from tenspiler.axioms import vec_elemwise_add_axiom, vec_scalar_mul_axiom
from tenspiler.codegen.utils import DataType
from tenspiler.tree_parser import analyze_single_loop
from tenspiler.utils.synthesis_utils import run_synthesis_algorithm

if __name__ == "__main__":
    driver, input_vars, lmsfir2 = analyze_single_loop(
        file_path="tenspiler/c2taco/cpp/for_synthesis/utdsp/lmsfir2.cc",
        func_name="lmsfir2",
        axioms=[vec_elemwise_add_axiom, vec_scalar_mul_axiom],
    )
    NTAPS, input, coefficient, error = (
        input_vars["NTAPS"],
        input_vars["input"],
        input_vars["coefficient"],
        input_vars["error"],
    )
    driver.add_precondition(NTAPS >= 1)
    driver.add_precondition(input.len() >= NTAPS)
    driver.add_precondition(coefficient.len() >= NTAPS)

    lmsfir2(NTAPS, input, coefficient, error)
    run_synthesis_algorithm(
        driver=driver,
        data_type=DataType.INT32,
        benchmark_name="lmsfir2",
        has_relaxed=False,
    )
