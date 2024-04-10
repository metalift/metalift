import time
from collections import defaultdict
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tenspiler.tenspiler_common import call_vec_elemwise_mul, vec_elemwise_mul


def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [vec_elemwise_mul]


def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    arr, n = reads
    out = writes[0]
    vec = choose(arr[:n])
    return out == call_vec_elemwise_mul(vec, call_vec_elemwise_mul(vec, vec))


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    arr, n = reads
    out, i, _ = writes
    vec = choose(arr[:i])
    return and_objects(
        i >= 0,
        i <= n,
        out == call_vec_elemwise_mul(vec, call_vec_elemwise_mul(vec, vec)),
    )


if __name__ == "__main__":
    driver = Driver()
    cube_in_place = driver.analyze(
        "tenspiler/c2taco/cpp/for_synthesis/simpl_array/cube_in_place.ll",
        "tenspiler/c2taco/cpp/for_synthesis/simpl_array/cube_in_place.loops",
        "cube_in_place",
        target_lang,
        defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar,
    )

    arr = mlList(Int, "arr")
    n = Int("n")

    driver.add_var_objects([arr, n])
    driver.add_precondition(n >= 1)
    driver.add_precondition(arr.len() >= n)

    cube_in_place(arr, n)

    start_time = time.time()
    driver.synthesize(filename="cube_in_place", no_verify=True)
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
