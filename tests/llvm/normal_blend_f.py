from typing import List, Union

from mypy.nodes import Statement

from metalift.frontend.llvm import Driver
from metalift.ir import And, Bool, BoolLit, Call, Choose, Eq, Expr, FnDecl,FnDeclRecursive, Ge, Gt, Int, IntLit, Ite, Le, ListT, Lt, Var, Add, Mul, Sub, Implies
from tests.python.utils.utils import codegen

from gaudi_common import *

def ps_grammar(writes: List[Var], reads: List[Var]) -> Expr:
    # reads = [in_lst]
    #print("reads: ")
    #print(*reads)
    base = reads[0]
    active = reads[1]
    opacity = reads[2]
    #print("ps writes:")
    #print(*writes)
    ret_val = writes[0]
    # give answer using reads[[#]]
    #Call("list_eq", Bool(), ret_val, )
    return Implies(And(Eq(ml_list_length(base), ml_list_length(active)), Gt(ml_list_length(base), IntLit(0))),
        Call("list_eq", Bool(), ret_val, call_vector_add(call_scalar_mul(opacity, active), call_scalar_mul(Sub(IntLit(1), opacity), base))))

def inv_grammar(writes: List[Var], reads: List[Var]) -> Expr:
    print("writes: ")
    print(*writes)
    #return BoolLit(True)
    base = reads[0]
    active = reads[1]
    opacity = reads[2]
    agg_result = writes[0]
    ref_tmp = writes[1]
    i = writes[2]

    return Implies(And(Eq(ml_list_length(base), ml_list_length(active)),
                           Gt(ml_list_length(base), IntLit(0))),
                       And(Ge(i, IntLit(0)),
                           Le(i, ml_list_length(active)),
                           Eq(agg_result,
                              call_vector_add(call_scalar_mul(opacity, ml_list_take(active, i)),
                                    call_scalar_mul(Sub(IntLit(1), opacity), ml_list_take(base, i)))
                              )))

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

    base_var = driver.variable("base", ListT(Int()))
    active_var = driver.variable("active", ListT(Int()))
    opacity_var = driver.variable("opacity", Int())

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
    base_var = driver.variable("base", ListT(Int()))
    active_var = driver.variable("active", ListT(Int()))
    opacity_var = driver.variable("opacity", Int())

    normal_blend_8(base_var, active_var, opacity_var)
    driver.synthesize(noVerify=True)