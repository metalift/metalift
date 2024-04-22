import time
from collections import defaultdict
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tenspiler.tenspiler_common import (
    call_vec_elemwise_add,
    call_vec_elemwise_mul,
    vec_elemwise_add,
    vec_elemwise_mul,
)


def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [vec_elemwise_add, vec_elemwise_mul]


def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    N, A, B, C = reads
    D = writes[0]
    vec = choose(A[:N], B[:N], C[:N])
    return D == call_vec_elemwise_add(call_vec_elemwise_mul(vec, vec), vec)


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    N, A, B, C = reads
    D, _, i = writes
    vec = choose(A[:i], B[:i], C[:i])
    return and_objects(
        i >= 0,
        i <= N,
        D == call_vec_elemwise_add(vec, call_vec_elemwise_mul(vec, vec)),
    )


if __name__ == "__main__":
    driver = Driver()
    n_real_updates = driver.analyze(
        "tenspiler/c2taco/cpp/for_synthesis/dspstone/n_real_updates.ll",
        "tenspiler/c2taco/cpp/for_synthesis/dspstone/n_real_updates.loops",
        "n_real_updates",
        target_lang,
        defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar,
    )

    N = Int("N")
    A = mlList(Int, "A")
    B = mlList(Int, "B")
    C = mlList(Int, "C")

    driver.add_var_objects([N, A, B, C])
    driver.add_precondition(N >= 1)
    driver.add_precondition(A.len() >= N)
    driver.add_precondition(B.len() >= N)
    driver.add_precondition(C.len() >= N)

    n_real_updates(N, A, B, C)

    start_time = time.time()
    driver.synthesize(filename="n_real_updates", no_verify=True)
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
