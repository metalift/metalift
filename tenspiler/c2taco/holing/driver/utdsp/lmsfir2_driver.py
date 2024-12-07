import time
from collections import defaultdict
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tenspiler.axioms import vec_elemwise_add_axiom, vec_scalar_mul_axiom
from tenspiler.codegen.utils import DataType
from tenspiler.tenspiler_common import (
    call_vec_elemwise_add,
    call_vec_scalar_mul,
    vec_elemwise_add,
    vec_scalar_mul,
)
from tenspiler.utils.synthesis_utils import run_synthesis_algorithm


def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        vec_elemwise_add,
        vec_scalar_mul,
        vec_elemwise_add_axiom,
        vec_scalar_mul_axiom,
    ]


def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    ntaps, input, coefficient, error = reads
    out = writes[0]
    vec = choose(input[: ntaps - 1], coefficient[: ntaps - 1])
    scalar = choose(error)
    return out == call_vec_elemwise_add(vec, call_vec_scalar_mul(scalar, vec))


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    ntaps, input, coefficient, error = reads
    out, _, i = writes
    vec = choose(input[:i], coefficient[:i])
    scalar = choose(error)
    return and_objects(
        i >= 0,
        i <= ntaps - 1,
        out == call_vec_elemwise_add(vec, call_vec_scalar_mul(scalar, vec)),
    )


if __name__ == "__main__":
    driver = Driver()
    lmsfir2 = driver.analyze(
        "tenspiler/c2taco/cpp/for_synthesis/utdsp/lmsfir2.ll",
        "tenspiler/c2taco/cpp/for_synthesis/utdsp/lmsfir2.loops",
        "lmsfir2",
        target_lang,
        defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar,
    )

    ntaps = Int("NTAPS")
    input = mlList(Int, "input")
    coefficient = mlList(Int, "coefficient")
    error = Int("error")

    driver.add_var_objects([ntaps, input, coefficient, error])
    driver.add_precondition(ntaps >= 1)
    driver.add_precondition(input.len() >= ntaps)
    driver.add_precondition(coefficient.len() >= ntaps)

    start_time = time.time()
    lmsfir2(ntaps, input, coefficient, error)
    run_synthesis_algorithm(
        driver=driver,
        data_type=DataType.INT32,
        benchmark_name="lmsfir2",
        has_relaxed=False,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
