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
    base, active, opacity = reads
    out = writes[0]
    cons = choose(Int(1))
    int_var = choose(opacity)
    vec_var = choose(base, active)
    return out == call_vec_elemwise_add(
        call_vec_scalar_mul(int_var, vec_var),
        call_vec_scalar_mul(cons - int_var, vec_var),
    )


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    base, active, opacity = reads
    out = writes[0]
    i = writes[1]

    cons = choose(Int(1))
    int_var = choose(opacity)
    vec_var = choose(base[:i], active[:i])
    return and_objects(
        i >= 0,
        i <= base.len(),
        out
        == call_vec_elemwise_add(
            call_vec_scalar_mul(int_var, vec_var),
            call_vec_scalar_mul(cons - int_var, vec_var),
        ),
    )


if __name__ == "__main__":
    driver = Driver()
    normal_blend_f = driver.analyze(
        "tenspiler/blend/cpp/for_synthesis/normal_blend_f.ll",
        "tenspiler/blend/cpp/for_synthesis/normal_blend_f.loops",
        "normal_blend_f",
        target_lang,
        defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar,
    )

    base_var = mlList(Int, "base")
    active_var = mlList(Int, "active")
    opacity_var = Int("opacity")
    driver.add_var_objects([base_var, active_var, opacity_var])
    driver.add_precondition(base_var.len() == active_var.len())
    driver.add_precondition(base_var.len() > 0)

    start_time = time.time()
    normal_blend_f(base_var, active_var, opacity_var)
    run_synthesis_algorithm(
        driver=driver,
        data_type=DataType.FLOAT,
        benchmark_name="normal_blend_f",
        has_relaxed=False,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
