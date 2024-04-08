import time
from collections import defaultdict
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tenspiler.tenspiler_common import call_vec_scalar_add, vec_scalar_add


def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [vec_scalar_add]


def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    arr, v, n = reads
    out = writes[0]
    vec = choose(arr[:n])
    scalar = choose(v)
    return out == call_vec_scalar_add(scalar, vec)


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    arr, v, n = reads
    out, i, _ = writes
    vec = choose(arr[:i])
    scalar = choose(v)
    return and_objects(i >= 0, i <= n, out == call_vec_scalar_add(scalar, vec))


if __name__ == "__main__":
    driver = Driver()
    voffset = driver.analyze(
        "tenspiler/c2taco/cpp/for_synthesis/dsp/voffset.ll",
        "tenspiler/c2taco/cpp/for_synthesis/dsp/voffset.loops",
        "voffset",
        target_lang,
        defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar,
    )

    arr = mlList(Int, "arr")
    v = Int("v")
    n = Int("n")

    driver.add_var_objects([arr, v, n])
    driver.add_precondition(n >= 1)
    driver.add_precondition(arr.len() >= n)

    voffset(arr, v, n)

    start_time = time.time()
    driver.synthesize(filename="voffset", no_verify=True)
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
