from typing import List

from mypy.nodes import Statement

from metalift.frontend.llvm import Driver
from metalift.ir import (Add, Call, Choose, Eq, Expr, FnDecl, FnDeclRecursive,
                         Int, IntLit, Ite, Lt, Mul, Sub, Tuple, TupleGet,
                         TupleT, Var)
from tests.python.utils.utils import codegen

L1_NORM = "l1_norm"
MAT_MUL = "mat_mul"

def target_lang() -> List[FnDeclRecursive]:
    a = Var("a", TupleT(Int(), Int()))
    b = Var("b", TupleT(Int(), Int()))
    x = Var("x", TupleT(Int(), Int()))
    p0l = Mul(TupleGet(a, IntLit(0)), TupleGet(x, IntLit(0)))
    p0r = Mul(TupleGet(b, IntLit(0)), TupleGet(x, IntLit(1)))
    p1l = Mul(TupleGet(a, IntLit(1)), TupleGet(x, IntLit(0)))
    p1r = Mul(TupleGet(b, IntLit(1)), TupleGet(x, IntLit(1)))
    mat_mul_body = Tuple(Add(p0l, p0r), Add(p1l, p1r))
    mat_mul = FnDecl(MAT_MUL, TupleT(Int(), Int()), mat_mul_body, a, b, x)

    p = Var("p", TupleT(Int(), Int()))
    p0 = TupleGet(p, IntLit(0))
    p1 = TupleGet(p, IntLit(1))
    p0_abs = Ite(Lt(p0, IntLit(0)), Sub(IntLit(0), p0), p0)
    p1_abs = Ite(Lt(p1, IntLit(0)), Sub(IntLit(0), p1), p1)
    l1_norm_body = Add(p0_abs, p1_abs)
    l1_norm = FnDecl(L1_NORM, Int(), l1_norm_body, p)

    return [mat_mul, l1_norm]


def ps_grammar(ret_val: Var, writes: List[Var], reads: List[Var]) -> Expr:
    a0, a1, b0, b1, x0, x1 = reads
    # Calculate the matrix-vector product
    a = Tuple(a0, a1)
    b = Tuple(b0, b1)
    x = Tuple(x0, x1)
    p = Call(MAT_MUL, TupleT(Int(), Int()), a, b, x)
    wrong_p = Call(MAT_MUL, TupleT(Int(), Int()), b, a, x)
    wrong_p2 = Call(MAT_MUL, TupleT(Int(), Int()), a, x,  b)

    # this is the correct answer
    l1_norm_p = Call(L1_NORM, Int(), p)
    # this is a wrong answer
    l1_norm_wrong_p = Call(L1_NORM, Int(), wrong_p)
    # this is a wrong answer
    l1_norm_wrong_p2 = Call(L1_NORM, Int(), wrong_p2)

    return Eq(ret_val, Choose(l1_norm_p, l1_norm_wrong_p, l1_norm_wrong_p2))

def inv_grammar(v: Var, writes: List[Var], reads: List[Var]) -> Expr:
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

    a0 = driver.variable("a0", Int())
    a1 = driver.variable("a1", Int())
    b0 = driver.variable("b0", Int())
    b1 = driver.variable("b1", Int())
    x0 = driver.variable("x0", Int())
    x1 = driver.variable("x1", Int())

    test(a0, a1, b0, b1, x0, x1)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))
