from tenspiler.axioms import vec_elemwise_add_axiom, vec_scalar_mul_axiom
from tenspiler.codegen.utils import DataType
from tenspiler.tree_parser import analyze_single_loop
from tenspiler.utils.synthesis_utils import run_synthesis_algorithm

if __name__ == "__main__":
    driver, input_vars, mult_add_into_cpu = analyze_single_loop(
        file_path="tenspiler/c2taco/cpp/for_synthesis/darknet/mult_add_into_cpu.cc",
        func_name="mult_add_into_cpu",
        axioms=[vec_elemwise_add_axiom, vec_scalar_mul_axiom],
    )
    N, X, Y, Z = input_vars["N"], input_vars["X"], input_vars["Y"], input_vars["Z"]
    driver.add_precondition(N >= 1)
    driver.add_precondition(X.len() >= N)
    driver.add_precondition(Y.len() >= N)
    driver.add_precondition(Z.len() >= N)
    mult_add_into_cpu(N, X, Y, Z)
    run_synthesis_algorithm(
        driver=driver,
        data_type=DataType.INT32,
        benchmark_name="mult_add_into_cpu",
        has_relaxed=False,
    )
