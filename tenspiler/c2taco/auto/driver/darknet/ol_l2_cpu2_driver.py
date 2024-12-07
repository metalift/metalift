from tenspiler.axioms import vec_elemwise_add_axiom, vec_elemwise_sub_axiom
from tenspiler.codegen.utils import DataType
from tenspiler.tree_parser import analyze_single_loop
from tenspiler.utils.synthesis_utils import run_synthesis_algorithm

if __name__ == "__main__":
    driver, input_vars, ol_l2_cpu2 = analyze_single_loop(
        file_path="tenspiler/c2taco/cpp/for_synthesis/darknet/ol_l2_cpu2.cc",
        func_name="ol_l2_cpu2",
        axioms=[vec_elemwise_add_axiom, vec_elemwise_sub_axiom],
    )
    n, pred, truth = input_vars["n"], input_vars["pred"], input_vars["truth"]
    driver.add_precondition(n >= 1)
    driver.add_precondition(pred.len() >= n)
    driver.add_precondition(truth.len() >= n)
    ol_l2_cpu2(n, pred, truth)
    run_synthesis_algorithm(
        driver=driver,
        data_type=DataType.INT32,
        benchmark_name="ol_l2_cpu2",
        has_relaxed=False,
    )
