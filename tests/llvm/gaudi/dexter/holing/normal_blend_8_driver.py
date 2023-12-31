from collections import defaultdict
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tests.llvm.gaudi.gaudi_common import (call_vec_elemwise_add,
                                           call_vec_scalar_mul,
                                           vec_elemwise_add, vec_scalar_mul)
from tests.python.utils.utils import codegen


def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [vec_elemwise_add, vec_scalar_mul]

def ps_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    base = reads[0]
    active = reads[1]
    opacity = reads[2]
    ret_val = writes[0]
    return ret_val == call_vec_elemwise_add(
        call_vec_scalar_mul(opacity, active),
        choose(
            call_vec_scalar_mul(1 - opacity, base),
            call_vec_scalar_mul(255 - opacity, base)
        )
    )

def inv_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    base = reads[0]
    active = reads[1]
    opacity = reads[2]
    agg_result = writes[0]
    i = writes[1]

    return and_objects(
        i >= 0,
        i <= active.len(),
        agg_result == call_vec_elemwise_add(
            call_vec_scalar_mul(opacity, active[:i]),
            choose(
                call_vec_scalar_mul(1 - opacity, base[:i]),
                call_vec_scalar_mul(255 - opacity, base[:i])
            )
        )
    )

if __name__ == "__main__":
    driver = Driver()
    normal_blend_f = driver.analyze(
        "tests/llvm/gaudi/normal_blend_f.ll",
        "tests/llvm/gaudi/normal_blend_f.loops",
        "test",
        target_lang,
        defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar
    )

    base_var = mlList(Int, "base")
    active_var = mlList(Int, "active")
    opacity_var = Int("opacity")
    driver.add_var_objects([base_var, active_var, opacity_var])
    driver.add_precondition(base_var.len() == active_var.len())
    driver.add_precondition(base_var.len() > 0)

    normal_blend_f(base_var, active_var, opacity_var)

    driver.synthesize(noVerify=True)

    print("\n\ngenerated code:" + normal_blend_f.codegen(codegen))

    def print_line():
        print("--------------------------------------------")
        print("--------------------------------------------")
        print("--------------------------------------------")
    print_line()

    driver = Driver()
    normal_blend_8 = driver.analyze(
        "tests/llvm/gaudi/normal_blend_8.ll",
        "tests/llvm/gaudi/normal_blend_8.loops",
        "normal_blend_8",
        target_lang,
        defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar
    )
    base_var = mlList(Int, "base")
    active_var = mlList(Int, "active")
    opacity_var = Int("opacity")
    driver.add_var_objects([base_var, active_var, opacity_var])
    driver.add_precondition(base_var.len() == active_var.len())
    driver.add_precondition(base_var.len() > 0)

    normal_blend_8(base_var, active_var, opacity_var)
    driver.synthesize(noVerify=True)

    print("\n\ngenerated code:" + normal_blend_8.codegen(codegen))