import time
from collections import defaultdict
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tenspiler.codegen.utils import DataType
from tenspiler.tenspiler_common import call_vec_scalar_mul, vec_scalar_mul
from tenspiler.utils.synthesis_utils import run_synthesis_algorithm
from tenspiler.axioms_tenspiler import vec_scalar_mul_axiom


def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [vec_scalar_mul, vec_scalar_mul_axiom]


def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    arr, v, n = reads
    out = writes[0]
    vec = choose(arr[:n])
    scalar = choose(v)
    return out == call_vec_scalar_mul(scalar, vec)


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    arr, v, n = reads
    out, i, _ = writes
    vec = choose(arr[:i])
    scalar = choose(v)
    return and_objects(i >= 0, i <= n, out == call_vec_scalar_mul(scalar, vec))


if __name__ == "__main__":
    driver = Driver()
    vscal = driver.analyze(
        "tenspiler/c2taco/cpp/for_synthesis/dsp/vscal.ll",
        "tenspiler/c2taco/cpp/for_synthesis/dsp/vscal.loops",
        "vscal",
        target_lang,
        defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar,
    )

    arr = mlList(Int, "arr")
    v = Int("v")
    n = Int("n")

    driver.add_var_objects([arr, v, n])
    driver.add_precondition(n >= 1)
    driver.add_precondition(arr.len() >= n)

    start_time = time.time()
    vscal(arr, v, n)
    run_synthesis_algorithm(
        driver=driver,
        data_type=DataType.INT32,
        benchmark_name="vscal",
        has_relaxed=False,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
