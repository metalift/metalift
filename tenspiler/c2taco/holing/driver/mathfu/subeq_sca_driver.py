import time
from collections import defaultdict
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tenspiler.tenspiler_common import call_vec_scalar_sub, vec_scalar_sub


def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [vec_scalar_sub]


def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    a, b, n = reads
    out = writes[0]
    vec = choose(a[:n])
    scalar = choose(b)
    return out == call_vec_scalar_sub(scalar, vec)


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    a, b, n = reads
    out, i, _ = writes
    vec = choose(a[:i])
    scalar = choose(b)
    return and_objects(i >= 0, i <= n, out == call_vec_scalar_sub(scalar, vec))


if __name__ == "__main__":
    driver = Driver()
    subeq_sca = driver.analyze(
        "tenspiler/c2taco/cpp/for_synthesis/mathfu/subeq_sca.ll",
        "tenspiler/c2taco/cpp/for_synthesis/mathfu/subeq_sca.loops",
        "subeq_sca",
        target_lang,
        defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar,
    )

    a = mlList(Int, "a")
    b = Int("b")
    n = Int("n")

    driver.add_var_objects([a, b, n])
    driver.add_precondition(n >= 1)
    driver.add_precondition(a.len() >= n)

    subeq_sca(a, b, n)

    start_time = time.time()
    driver.synthesize(filename="subeq_sca", no_verify=True)
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
