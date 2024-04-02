import time
from collections import defaultdict
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tenspiler.tenspiler_common import (
    get_matrix_or_vec_expr_eq_or_below_depth,
    scalar_vec_to_vec_target_lang,
    vec_vec_to_vec_target_lang,
)
from tests.python.utils.utils import codegen


def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [*vec_vec_to_vec_target_lang, *scalar_vec_to_vec_target_lang]


def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    base, active, opacity = reads
    out = writes[0]
    cons = choose(Int(255))
    vec_var = choose(base, active)
    return out == get_matrix_or_vec_expr_eq_or_below_depth(
        matrix_or_vec_var=vec_var, int_vars=[opacity, Int(255)], depth=3
    )


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    base, active, opacity = reads
    out = writes[0]
    i = writes[1]

    cons = choose(Int(255))
    vec_var = choose(base[:i], active[:i])
    return and_objects(
        i >= 0,
        i <= base.len(),
        out
        == get_matrix_or_vec_expr_eq_or_below_depth(
            matrix_or_vec_var=vec_var, int_vars=[opacity, Int(255)], depth=3
        ),
    )


if __name__ == "__main__":
    driver = Driver()
    normal_blend_8 = driver.analyze(
        "tenspiler/dexter/cpp/for_synthesis/normal_blend_8.ll",
        "tenspiler/dexter/cpp/for_synthesis/normal_blend_8.loops",
        "normal_blend_8",
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

    normal_blend_8(base_var, active_var, opacity_var)

    start_time = time.time()
    driver.synthesize()
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
    print("\n\ngenerated code:" + normal_blend_8.codegen(codegen))
