import time
from collections import defaultdict
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tenspiler.axioms import vec_elemwise_add_axiom, vec_elemwise_sub_axiom
from tenspiler.codegen.utils import DataType
from tenspiler.tenspiler_common import (
    call_vec_elemwise_sub,
    vec_elemwise_add,
    vec_elemwise_sub,
)
from tenspiler.utils.synthesis_utils import run_synthesis_algorithm


def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        vec_elemwise_add,
        vec_elemwise_sub,
        vec_elemwise_add_axiom,
        vec_elemwise_sub_axiom,
    ]


def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    n, pred, truth = reads
    delta = writes[0]
    vec = choose(truth[:n], pred[:n])
    return delta == call_vec_elemwise_sub(vec, vec)


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    n, pred, truth = reads
    delta, _, i = writes
    vec = choose(truth[:i], pred[:i])
    return and_objects(i >= 0, i <= n, delta == call_vec_elemwise_sub(vec, vec))


if __name__ == "__main__":
    driver = Driver()
    ol_l2_cpu2 = driver.analyze(
        "tenspiler/c2taco/cpp/for_synthesis/darknet/ol_l2_cpu2.ll",
        "tenspiler/c2taco/cpp/for_synthesis/darknet/ol_l2_cpu2.loops",
        "ol_l2_cpu2",
        target_lang,
        defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar,
    )

    n = Int("n")
    pred = mlList(Int, "pred")
    truth = mlList(Int, "truth")

    driver.add_var_objects([n, pred, truth])
    driver.add_precondition(n >= 1)
    driver.add_precondition(pred.len() >= n)
    driver.add_precondition(truth.len() >= n)

    start_time = time.time()
    ol_l2_cpu2(n, pred, truth)
    run_synthesis_algorithm(
        driver=driver,
        data_type=DataType.INT32,
        benchmark_name="ol_l2_cpu2",
        has_relaxed=False,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
