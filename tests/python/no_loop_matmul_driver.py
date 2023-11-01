from typing import List

from metalift.frontend.python import Driver
from metalift.ir import (FnDecl, FnDeclRecursive, IntObject, NewObject, TupleObject, call, choose, ite, make_tuple, make_tuple_type)
from tests.python.utils.utils import codegen

L1_NORM = "l1_norm"
MAT_MUL = "mat_mul"
TWO_INT_TUPLE_TYPE = make_tuple_type(IntObject, IntObject)

def target_lang() -> List[FnDeclRecursive]:
    a = TupleObject(IntObject, IntObject, "a")
    b = TupleObject(IntObject, IntObject, "b")
    x = TupleObject(IntObject, IntObject, "x")
    p0l = a[0] * x[0]
    p0r = b[0] * x[1]
    p1l = a[1] * x[0]
    p1r = b[1] * x[1]
    mat_mul_body = make_tuple(p0l + p0r, p1l + p1r)
    mat_mul = FnDecl(MAT_MUL, TWO_INT_TUPLE_TYPE, mat_mul_body.src, a.src, b.src, x.src)

    p = TupleObject(IntObject, IntObject, "p")
    p0 = p[0]
    p1 = p[1]
    p0_abs = ite(p0 < 0, 0 - p0, p0)
    p1_abs = ite(p1 < 0, 0 - p1, p1)
    l1_norm_body = p0_abs + p1_abs
    l1_norm = FnDecl(L1_NORM, IntObject, l1_norm_body.src, p.src)

    return [mat_mul, l1_norm]


def ps_grammar(ret_val: NewObject, writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> NewObject:
    a0, a1, b0, b1, x0, x1 = reads
    # Calculate the matrix-vector product
    a = make_tuple(a0, a1)
    b = make_tuple(b0, b1)
    x = make_tuple(x0, x1)
    p = call(MAT_MUL, TWO_INT_TUPLE_TYPE, a, b, x)
    wrong_p = call(MAT_MUL, TWO_INT_TUPLE_TYPE, b, a, x)
    wrong_p2 = call(MAT_MUL, TWO_INT_TUPLE_TYPE, a, x,  b)

    # this is the correct answer
    l1_norm_p = call(L1_NORM, IntObject, p)
    # this is a wrong answer
    l1_norm_wrong_p = call(L1_NORM, IntObject, wrong_p)
    # this is a wrong answer
    l1_norm_wrong_p2 = call(L1_NORM, IntObject, wrong_p2)

    return ret_val == choose(l1_norm_p, l1_norm_wrong_p, l1_norm_wrong_p2)

def inv_grammar(v: NewObject, writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> NewObject:
    raise Exception("no loop in the source")

if __name__ == "__main__":
    filename = "tests/python/no_loop_matmul.py"

    driver = Driver()
    test = driver.analyze(filename, "test", target_lang, inv_grammar, ps_grammar)

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
