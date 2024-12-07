import time
from collections import defaultdict
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tenspiler.axioms import reduce_sum_axiom, vec_elemwise_mul_axiom
from tenspiler.codegen.utils import DataType
from tenspiler.tenspiler_common import (
    call_reduce_sum,
    call_vec_elemwise_mul,
    reduce_sum,
    vec_elemwise_mul,
)
from tenspiler.utils.synthesis_utils import run_synthesis_algorithm


def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [reduce_sum, vec_elemwise_mul, reduce_sum_axiom, vec_elemwise_mul_axiom]


def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    a, n = reads
    sum = writes[0]
    vec = choose(a[:n])
    return sum == call_reduce_sum(call_vec_elemwise_mul(vec, vec))


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    a, n = reads
    i, sum = writes
    vec = choose(a[:i])
    return and_objects(
        i >= 0, i <= n, sum == call_reduce_sum(call_vec_elemwise_mul(vec, vec))
    )


if __name__ == "__main__":
    driver = Driver()
    mse_array = driver.analyze(
        "tenspiler/c2taco/cpp/for_synthesis/darknet/mse_array.ll",
        "tenspiler/c2taco/cpp/for_synthesis/darknet/mse_array.loops",
        "mse_array",
        target_lang,
        defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar,
    )

    a = mlList(Int, "a")
    n = Int("n")

    driver.add_var_objects([a, n])
    driver.add_precondition(n >= 1)
    driver.add_precondition(a.len() > 0)
    driver.add_precondition(a.len() >= n)

    start_time = time.time()
    mse_array(a, n)
    run_synthesis_algorithm(
        driver=driver,
        data_type=DataType.INT32,
        benchmark_name="mse_array",
        has_relaxed=False,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
