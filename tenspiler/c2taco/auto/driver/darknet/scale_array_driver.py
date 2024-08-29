from collections import defaultdict
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Object
from tenspiler.axioms_tenspiler import vec_scalar_mul_axiom
from tenspiler.codegen.utils import DataType
from tenspiler.tenspiler_common import vec_scalar_mul
from tenspiler.tree_parser import (
    find_compute_from_file,
    find_root_node_from_file,
    get_outer_loop_inv,
    get_ps,
    make_input_variables,
)
from tenspiler.utils.synthesis_utils import run_synthesis_algorithm


def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [vec_scalar_mul, vec_scalar_mul_axiom]


def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    ps_cond = get_ps(
        writes=writes,
        reads=reads,
        in_scope=in_scope,
        relaxed=relaxed,
        loop_bounds=[[("i", 0), ("i", "<", "n")]],
        compute_node=compute,
    )
    return ps_cond


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    return get_outer_loop_inv(
        writes=writes,
        reads=reads,
        in_scope=in_scope,
        relaxed=relaxed,
        loop_bounds=[[("i", 0), ("i", "<", "n")]],
        compute_node=compute,
    )


if __name__ == "__main__":
    driver = Driver()
    file_path = "tenspiler/c2taco/cpp/for_synthesis/darknet/scale_array.cc"
    root_node = find_root_node_from_file(file_path)
    input_vars = make_input_variables(root_node, driver)
    compute = find_compute_from_file(file_path)

    scale_array = driver.analyze(
        "tenspiler/c2taco/cpp/for_synthesis/darknet/scale_array.ll",
        "tenspiler/c2taco/cpp/for_synthesis/darknet/scale_array.loops",
        "scale_array",
        target_lang,
        defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar,
    )

    a, n, s = input_vars["a"], input_vars["n"], input_vars["s"]
    driver.add_precondition(n >= 1)
    driver.add_precondition(a.len() >= n)
    scale_array(a, n, s)
    run_synthesis_algorithm(
        driver=driver,
        data_type=DataType.INT32,
        benchmark_name="scale_array",
        has_relaxed=False,
    )
