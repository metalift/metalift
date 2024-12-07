from tenspiler.axioms import reduce_sum_axiom, vec_elemwise_mul_axiom
from tenspiler.codegen.utils import DataType
from tenspiler.tree_parser import analyze_single_loop
from tenspiler.utils.synthesis_utils import run_synthesis_algorithm

if __name__ == "__main__":
    driver, input_vars, lmsfir1 = analyze_single_loop(
        file_path="tenspiler/c2taco/cpp/for_synthesis/utdsp/lmsfir1.cc",
        func_name="lmsfir1",
        axioms=[reduce_sum_axiom, vec_elemwise_mul_axiom],
    )
    NTAPS, input, coefficient = (
        input_vars["NTAPS"],
        input_vars["input"],
        input_vars["coefficient"],
    )
    driver.add_precondition(NTAPS >= 1)
    driver.add_precondition(input.len() >= NTAPS)
    driver.add_precondition(coefficient.len() >= NTAPS)

    lmsfir1(NTAPS, input, coefficient)
    run_synthesis_algorithm(
        driver=driver,
        data_type=DataType.INT32,
        benchmark_name="lmsfir1",
        has_relaxed=False,
    )
