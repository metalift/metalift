import time
from collections import defaultdict
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tenspiler.codegen.utils import DataType
from tenspiler.tenspiler_common import call_vec_scalar_add, vec_scalar_add
from tenspiler.utils.synthesis_utils import run_synthesis_algorithm
from tenspiler.axioms_tenspiler import vec_scalar_add_axiom


def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [vec_scalar_add, vec_scalar_add_axiom]


def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    arr, n = reads
    out = writes[0]
    vec = choose(arr[:n])
    return out == call_vec_scalar_add(Int(1), vec)


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    arr, n = reads
    out, i, _ = writes
    vec = choose(arr[:i])
    return and_objects(i >= 0, i <= n, out == call_vec_scalar_add(Int(1), vec))


if __name__ == "__main__":
    driver = Driver()
    array_inc = driver.analyze(
        "tenspiler/c2taco/cpp/for_synthesis/simpl_array/array_inc.ll",
        "tenspiler/c2taco/cpp/for_synthesis/simpl_array/array_inc.loops",
        "array_inc",
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
    array_inc(arr, n)
    run_synthesis_algorithm(
        driver=driver,
        data_type=DataType.INT32,
        benchmark_name="array_inc",
        has_relaxed=False,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
