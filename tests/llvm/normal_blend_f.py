from typing import List

from metalift.frontend.llvm import Driver
from metalift.ir import Expr, NewObject, implies
from metalift.vc_util import and_objects
from tests.python.utils.utils import codegen

from gaudi_common import *

def ps_grammar(writes: List[NewObject], reads: List[NewObject]) -> NewObject:
    base = reads[0]
    active = reads[1]
    opacity = reads[2]
    ret_val = writes[0]
    return implies(
        and_objects(base.len() == active.len(), base.len() > 0),
        ret_val == call_vector_add(
            call_scalar_mul(opacity, active),
            call_scalar_mul(1 - opacity, base)
        )
    )

def inv_grammar(writes: List[NewObject], reads: List[NewObject]) -> NewObject:
    print("writes: ")
    print(*writes)
    #return BoolLit(True)
    base = reads[0]
    active = reads[1]
    opacity = reads[2]
    agg_result = writes[0]
    ref_tmp = writes[1]
    i = writes[2]

    return implies(
        and_objects(base.len() == active.len(), base.len() > 0),
        and_objects(
            i >= 0,
            i <= active.len(),
            agg_result == call_vector_add(
                call_scalar_mul(opacity, active.take(i)),
                call_scalar_mul(1 - opacity, base.take(i))
            )
        )
    )

if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        "tests/llvm/normal_blend_f.ll",
        "tests/llvm/normal_blend_f.loops",
        "test",
        target_lang,
        inv_grammar,
        ps_grammar
    )

    base_var = ListObject(IntObject, "base")
    active_var = ListObject(IntObject, "active")
    opacity_var = IntObject("opacity")
    driver.add_var_objects([base_var, active_var, opacity_var])

    test(base_var, active_var, opacity_var)

    driver.synthesize(noVerify=True)

    print("\n\ngenerated code:" + test.codegen(codegen))

    def print_line():
        print("--------------------------------------------")
        print("--------------------------------------------")
        print("--------------------------------------------")
    print_line()

    driver = Driver()
    normal_blend_8 = driver.analyze(
        "tests/llvm/normal_blend_8.ll",
        "tests/llvm/normal_blend_8.loops",
        "normal_blend_8",
        target_lang,
        inv_grammar,
        ps_grammar
    )
    base_var = ListObject(IntObject, "base")
    active_var = ListObject(IntObject, "active")
    opacity_var = IntObject("opacity")

    normal_blend_8(base_var, active_var, opacity_var)
    driver.synthesize(noVerify=True)