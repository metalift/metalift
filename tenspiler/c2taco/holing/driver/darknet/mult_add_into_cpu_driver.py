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
    N, X, Y, Z = reads
    out = writes[0]
    vec = choose(X[:N], Y[:N], Z[:N])
    return out == call_vec_elemwise_add(vec, call_vec_elemwise_mul(vec, vec))


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    N, X, Y, Z = reads
    out, i, _ = writes
    vec = choose(X[:i], Y[:i], Z[:i])
    return and_objects(
        i >= 0,
        i <= N,
        out == call_vec_elemwise_add(vec, call_vec_elemwise_mul(vec, vec)),
    )


if __name__ == "__main__":
    driver = Driver()
    mult_add_into_cpu = driver.analyze(
        "tenspiler/c2taco/cpp/for_synthesis/darknet/mult_add_into_cpu.ll",
        "tenspiler/c2taco/cpp/for_synthesis/darknet/mult_add_into_cpu.loops",
        "mult_add_into_cpu",
        target_lang,
        defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar,
    )

    N = Int("N")
    X = mlList(Int, "X")
    Y = mlList(Int, "Y")
    Z = mlList(Int, "Z")

    driver.add_var_objects([N, X, Y, Z])
    driver.add_precondition(N >= 1)
    driver.add_precondition(X.len() >= N)
    driver.add_precondition(Y.len() >= N)
    driver.add_precondition(Z.len() >= N)

    mult_add_into_cpu(N, X, Y, Z)

    start_time = time.time()
    driver.synthesize(filename="mult_add_into_cpu", no_verify=True)
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
