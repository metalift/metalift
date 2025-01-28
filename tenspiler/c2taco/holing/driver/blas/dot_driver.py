import time
from collections import defaultdict
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tenspiler.codegen.utils import Backend, DataType
from tenspiler.tenspiler_common import (
    call_reduce_sum,
    call_vec_elemwise_mul,
    reduce_sum,
    vec_elemwise_mul,
)
from tenspiler.utils.synthesis_utils import run_synthesize_algorithm


def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [reduce_sum, vec_elemwise_mul]


def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    a, b, n = reads
    sum = writes[0]
    vec = choose(a[:n], b[:n])
    return sum == call_reduce_sum(call_vec_elemwise_mul(vec, vec))


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    a, b, n = reads
    i, sum = writes
    vec = choose(a[:i], b[:i])
    return and_objects(
        i >= 0, i <= n, sum == call_reduce_sum(call_vec_elemwise_mul(vec, vec))
    )


if __name__ == "__main__":
    driver = Driver()
    dot = driver.analyze(
        "tenspiler/c2taco/cpp/for_synthesis/blas/dot.ll",
        "tenspiler/c2taco/cpp/for_synthesis/blas/dot.loops",
        "dot",
        target_lang,
        defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar,
    )

    a = mlList(Int, "a")
    b = mlList(Int, "b")
    n = Int("n")

    driver.add_var_objects([a, b, n])
    driver.add_precondition(n >= 1)
    driver.add_precondition(a.len() > 0)
    driver.add_precondition(a.len() >= n)
    driver.add_precondition(b.len() > 0)
    driver.add_precondition(b.len() >= n)

    start_time = time.time()
    dot(a, b, n)
    run_synthesize_algorithm(
        driver=driver,
        backend=Backend.NUMPY,
        data_type=DataType.INT32,
        benchmark_name="dot",
        list_bound_start=2,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
