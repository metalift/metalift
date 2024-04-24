import time
from collections import defaultdict
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tenspiler.codegen.utils import DataType
from tenspiler.tenspiler_common import call_scalar_vec_div, scalar_vec_div
from tenspiler.utils.synthesis_utils import run_synthesis_algorithm
from tenspiler.axioms_tenspiler import scalar_vec_div_axiom


def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [scalar_vec_div, scalar_vec_div_axiom]


def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    arr, n = reads
    out = writes[0]
    vec = choose(arr[:n])
    return out == call_scalar_vec_div(Int(1), vec)


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    arr, n = reads
    out, i, _ = writes
    vec = choose(arr[:i])
    return and_objects(i >= 0, i <= n, out == call_scalar_vec_div(Int(1), vec))


if __name__ == "__main__":
    driver = Driver()
    vrecip = driver.analyze(
        "tenspiler/c2taco/cpp/for_synthesis/dsp/vrecip.ll",
        "tenspiler/c2taco/cpp/for_synthesis/dsp/vrecip.loops",
        "vrecip",
        target_lang,
        defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar,
    )

    arr = mlList(Int, "arr")
    n = Int("n")

    driver.add_var_objects([arr, n])
    driver.add_precondition(n >= 1)
    driver.add_precondition(arr.len() >= n)

    start_time = time.time()
    vrecip(arr, n)
    run_synthesis_algorithm(
        driver=driver,
        data_type=DataType.INT32,
        benchmark_name="vrecip",
        has_relaxed=False,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
