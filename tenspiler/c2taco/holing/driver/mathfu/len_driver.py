import time
from collections import defaultdict
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tenspiler.tenspiler_common import (
    call_reduce_sum,
    call_vec_elemwise_mul,
    reduce_sum,
    vec_elemwise_mul,
)


def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [reduce_sum, vec_elemwise_mul]


def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    arr, n = reads
    l = writes[0]
    vec = choose(arr[:n])
    return l == call_reduce_sum(call_vec_elemwise_mul(vec, vec))


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    arr, n = reads
    i, l = writes
    vec = choose(arr[:i])
    return and_objects(
        i >= 0, i <= n, l == call_reduce_sum(call_vec_elemwise_mul(vec, vec))
    )


if __name__ == "__main__":
    driver = Driver()
    len = driver.analyze(
        "tenspiler/c2taco/cpp/for_synthesis/mathfu/len.ll",
        "tenspiler/c2taco/cpp/for_synthesis/mathfu/len.loops",
        "len",
        target_lang,
        defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar,
    )

    arr = mlList(Int, "arr")
    n = Int("n")

    driver.add_var_objects([arr, n])
    driver.add_precondition(n >= 1)
    driver.add_precondition(arr.len() > 0)
    driver.add_precondition(arr.len() >= n)

    len(arr, n)

    start_time = time.time()
    driver.synthesize(filename="len", no_verify=True)
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
