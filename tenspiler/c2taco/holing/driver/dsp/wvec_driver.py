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
    call_vec_scalar_mul,
    vec_elemwise_add,
    vec_scalar_mul,
)


def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [vec_elemwise_add, vec_scalar_mul]


def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    a, b, m, n = reads
    out = writes[0]
    vec = choose(a[:n], b[:n])
    scalar = choose(m)
    return out == call_vec_elemwise_add(call_vec_scalar_mul(scalar, vec), vec)


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    a, b, m, n = reads
    out, i, _ = writes
    vec = choose(a[:i], b[:i])
    scalar = choose(m)
    return and_objects(
        i >= 0,
        i <= n,
        out == call_vec_elemwise_add(call_vec_scalar_mul(scalar, vec), vec),
    )


if __name__ == "__main__":
    driver = Driver()
    wvec = driver.analyze(
        "tenspiler/c2taco/cpp/for_synthesis/dsp/wvec.ll",
        "tenspiler/c2taco/cpp/for_synthesis/dsp/wvec.loops",
        "wvec",
        target_lang,
        defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar,
    )

    a = mlList(Int, "a")
    b = mlList(Int, "b")
    m = Int("m")
    n = Int("n")

    driver.add_var_objects([a, b, m, n])
    driver.add_precondition(n >= 1)
    driver.add_precondition(a.len() >= n)
    driver.add_precondition(b.len() >= n)

    wvec(a, b, m, n)

    start_time = time.time()
    driver.synthesize(filename="wvec", no_verify=True)
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
