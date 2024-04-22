import time
from collections import defaultdict
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tenspiler.codegen.utils import DataType
from tenspiler.utils.synthesis_utils import run_synthesis_algorithm


def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return []


def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    a, n = reads
    out = writes[0]
    vec = choose(a[:n])
    return out == vec


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    a, n = reads
    out, i = writes
    vec = choose(a[:i])
    return and_objects(i >= 0, i <= n, out == vec)


if __name__ == "__main__":
    driver = Driver()
    vcopy = driver.analyze(
        "tenspiler/c2taco/cpp/for_synthesis/dsp/vcopy.ll",
        "tenspiler/c2taco/cpp/for_synthesis/dsp/vcopy.loops",
        "vcopy",
        target_lang,
        defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar,
    )

    a = mlList(Int, "a")
    n = Int("n")

    driver.add_var_objects([a, n])
    driver.add_precondition(n >= 1)
    driver.add_precondition(a.len() >= n)

    start_time = time.time()
    vcopy(a, n)
    run_synthesis_algorithm(
        driver=driver,
        data_type=DataType.INT32,
        benchmark_name="vcopy",
        has_relaxed=False,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
