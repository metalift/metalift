from typing import List

from mypy.nodes import Statement

from metalift.frontend.llvm import Driver
from metalift.ir import (NewObject, Expr, FnDeclRecursive,
                         IntObject, Tuple, TupleObject, make_tuple, make_tuple_type, fnDecl, ite, call, choose)
from tests.python.utils.utils import codegen

L1_NORM = "l1_norm"
MAT_MUL = "mat_mul"

def target_lang() -> List[FnDeclRecursive]:
    a = TupleObject(IntObject, IntObject, "a")
    b = TupleObject(IntObject, IntObject, "b")
    x = TupleObject(IntObject, IntObject, "x")
    p0l = a[0] * x[0] 
    p0r = b[0] * x[1] 
    p1l = a[1] * x[0]
    p1r = b[1] * x[1] 
    mat_mul_body = make_tuple(p0l + p0r, p1l + p1r)
    mat_mul = fnDecl(MAT_MUL, make_tuple_type(IntObject, IntObject), mat_mul_body, a, b, x)

    p = TupleObject(IntObject, IntObject, "p")
    p0 = p[0]
    p1 = p[1]
    p0_abs = ite(p0 < 0,0 - p0, p0)
    p1_abs = ite(p1 < 0, 0 - p1, p1)
    l1_norm_body = p0_abs and p1_abs
    l1_norm = fnDecl(L1_NORM, IntObject, l1_norm_body, p)

    return [mat_mul, l1_norm]


def ps_grammar(ret_val: NewObject, writes: List[NewObject], reads: List[NewObject]) -> Expr:
    a0, a1, b0, b1, x0, x1 = reads
    # Calculate the matrix-vector product
    a_src = Tuple(a0, a1)
    a = TupleObject(IntObject, IntObject, a_src)
    b_src = Tuple(b0, b1)
    b = TupleObject(IntObject, IntObject, b_src)
    x_src = Tuple(x0, x1)
    x = TupleObject(IntObject, IntObject, x_src)
    p = call(MAT_MUL, make_tuple_type(IntObject, IntObject), a, b, x)
    wrong_p = call(MAT_MUL, make_tuple_type(IntObject, IntObject), b, a, x)
    wrong_p2 = call(MAT_MUL, make_tuple_type(IntObject, IntObject), a, x, b)

    # this is the correct answer
    l1_norm_p = call(L1_NORM, IntObject, p)
    # this is a wrong answer
    l1_norm_wrong_p = call(L1_NORM, IntObject, wrong_p)
    # this is a wrong answer
    l1_norm_wrong_p2 = call(L1_NORM, IntObject, wrong_p2)

    return ret_val == choose(l1_norm_p, l1_norm_wrong_p, l1_norm_wrong_p2)

def inv_grammar(v: NewObject, writes: List[NewObject], reads: List[NewObject]) -> Expr:
    raise Exception("no loop in the source")

if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        llvm_filepath="tests/llvm/no_loop_matmul.ll",
        loops_filepath="tests/llvm/no_loop_matmul.loops",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammar=inv_grammar,
        ps_grammar=ps_grammar
    )

    a0 = IntObject("a0")
    a1 = IntObject("a1")
    b0 = IntObject("b0")
    b1 = IntObject("b1")
    x0 = IntObject("x0")
    x1 = IntObject("x1")
    driver.add_var_objects([a0, a1, b0, b1, x0, x1])

    test(a0, a1, b0, b1, x0, x1)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))
