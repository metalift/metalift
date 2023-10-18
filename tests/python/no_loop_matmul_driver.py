from typing import List, Literal


from metalift.frontend.python import Driver
from metalift.ir import (Add, Call, Choose, Eq, Expr, FnDecl, FnDeclRecursive,
                        IntObject, Ite, Tuple, TupleObject, Var)
from tests.python.utils.utils import codegen

L1_NORM = "l1_norm"
MAT_MUL = "mat_mul"

def target_lang() -> List[FnDeclRecursive]:
    a = TupleObject[IntObject, Literal[2]](IntObject, Literal[2], "a")
    b = TupleObject[IntObject, Literal[2]](IntObject, Literal[2], "b")
    x = TupleObject[IntObject, Literal[2]](IntObject, Literal[2], "x")
    p0l = a[0] * x[0]
    p0r = b[0] * x[1]
    p1l = a[1] * x[0]
    p1r = b[1] * x[1]
    mat_mul_body_expr = Tuple(p0l + p0r, p1l + p1r)
    mat_mul_body = TupleObject[IntObject, Literal[2]](IntObject, Literal[2], mat_mul_body_expr)
    mat_mul = FnDecl(MAT_MUL, TupleObject[IntObject, Literal[2]], mat_mul_body, a, b, x)

    p = TupleObject[IntObject, Literal[2]](IntObject, Literal[2], "p")

    p0 = p[0]
    p1 = p[1]
    p0_abs = Ite(p0 < 0, IntObject(0) - p0, p0)
    p1_abs = Ite(p1 < 0, IntObject(0) - p1, p1)
    l1_norm_body = IntObject(Add(p0_abs, p1_abs))
    l1_norm = FnDecl(L1_NORM, IntObject, l1_norm_body, p)

    return [mat_mul, l1_norm]


def ps_grammar(ret_val: Var, writes: List[Var], reads: List[Var], in_scope: List[Var]) -> Expr:
    a0, a1, b0, b1, x0, x1 = reads
    # Calculate the matrix-vector product
    a = TupleObject[IntObject, Literal[2]](IntObject, Literal[2], Tuple(a0, a1))
    b = TupleObject[IntObject, Literal[2]](IntObject, Literal[2], Tuple(b0, b1))
    x = TupleObject[IntObject, Literal[2]](IntObject, Literal[2], Tuple(x0, x1))
    p = Call(MAT_MUL, TupleObject[IntObject, Literal[2]], a, b, x)
    wrong_p = Call(MAT_MUL, TupleObject[IntObject, Literal[2]], b, a, x)
    wrong_p2 = Call(MAT_MUL, TupleObject[IntObject, Literal[2]], a, x, b)

    # this is the correct answer
    l1_norm_p = Call(L1_NORM, IntObject, p)
    # this is a wrong answer
    l1_norm_wrong_p = Call(L1_NORM, IntObject, wrong_p)
    # this is a wrong answer
    l1_norm_wrong_p2 = Call(L1_NORM, IntObject, wrong_p2)

    return Eq(ret_val, Choose(l1_norm_p, l1_norm_wrong_p, l1_norm_wrong_p2))

def inv_grammar(v: Var, writes: List[Var], reads: List[Var], in_scope: List[Var]) -> Expr:
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
