from collections import defaultdict
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int, List as mlList, Object, choose
from metalift.vc_util import and_objects
from tests.llvm.gaudi.gaudi_common import (call_scalar_mul, call_vector_add)
from tests.python.utils.utils import codegen
from tests.llvm.gaudi.gaudi_common import vector_add, elemwise_mul, scalar_mul, broadcast_add, reduce_sum, reduce_mul

def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [vector_add, elemwise_mul, scalar_mul, broadcast_add, reduce_sum, reduce_mul]

def ps_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    base = reads[0]
    active = reads[1]
    opacity = reads[2]
    ret_val = writes[0]
    return ret_val == call_vector_add(
        call_scalar_mul(opacity, active),
        choose(
            call_scalar_mul(1 - opacity, base),
            call_scalar_mul(255 - opacity, base)
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
        agg_result == call_vector_add(
            call_scalar_mul(opacity, active[:i]),
            choose(
                call_scalar_mul(1 - opacity, base[:i]),
                call_scalar_mul(255 - opacity, base[:i])
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