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
    ntaps, input, coefficient = reads
    sum = writes[0]
    vec = choose(input[:ntaps], coefficient[:ntaps])
    return sum == call_reduce_sum(call_vec_elemwise_mul(vec, vec))


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    ntaps, input, coefficient = reads
    i, sum = writes
    vec = choose(input[:i], coefficient[:i])
    return and_objects(
        i >= 0, i <= ntaps, sum == call_reduce_sum(call_vec_elemwise_mul(vec, vec))
    )


if __name__ == "__main__":
    driver = Driver()
    fir_small = driver.analyze(
        "tenspiler/c2taco/cpp/for_synthesis/utdsp/fir_small.ll",
        "tenspiler/c2taco/cpp/for_synthesis/utdsp/fir_small.loops",
        "fir_small",
        target_lang,
        defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar,
    )

    ntaps = Int("NTAPS")
    input = mlList(Int, "input")
    coefficient = mlList(Int, "coefficient")

    driver.add_var_objects([ntaps, input, coefficient])
    driver.add_precondition(ntaps >= 1)
    driver.add_precondition(input.len() >= ntaps)
    driver.add_precondition(coefficient.len() >= ntaps)

    start_time = time.time()
    fir_small(ntaps, input, coefficient)
    run_synthesis_algorithm(
        driver=driver,
        data_type=DataType.INT32,
        benchmark_name="fir_small",
        has_relaxed=False,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
