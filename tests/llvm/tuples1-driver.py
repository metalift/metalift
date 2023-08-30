from typing import List

from metalift.frontend.llvm import Driver
from metalift.ir import (Add, Call, Choose, Eq, Expr, FnDecl, Int, 
                         FnDeclRecursive, IntLit, Mul, Sub, Tuple, TupleGet, TupleT, Var)
from tests.python.utils.utils import codegen

def tuple_mult(t):
    return Call("tuple_mult", Int(), t)

def target_lang():
    x = Var("x", TupleT(Int(), Int()))
    tuple_mult = FnDeclRecursive(
        "tuple_mult", Int(), Mul(TupleGet(x, IntLit(0)), TupleGet(x, IntLit(1))), x
    )
    return [tuple_mult]

def inv_grammar(v: Var, writes: List[Var], reads: List[Var]) -> Expr:
    raise Exception("no invariant")

def ps_grammar(ret_val: Var, writes: List[Var], reads: List[Var]) -> Expr:
    (x, y) = reads
    summary = Choose(
        Eq(ret_val, Add(tuple_mult(Tuple(x, x)), tuple_mult(Tuple(y, y)))),
        Eq(ret_val, Sub(tuple_mult(Tuple(x, x)), tuple_mult(Tuple(y, y)))),
    )
    return summary

if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        llvm_filepath="tests/llvm/tuples1.ll",
        loops_filepath="tests/llvm/tuples1.loops",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammar=inv_grammar,
        ps_grammar=ps_grammar
    )

    x = driver.variable("x", Int())
    y = driver.variable("y", Int())

    test(x, y)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))