from typing import List

from metalift.frontend.llvm import Driver
from metalift.ir import (Add, Call, Choose, Eq, Expr, FnDecl, Int,
                         FnDeclRecursive, IntLit, Mul, Sub, Tuple, TupleGet, TupleT, Var)
from tests.python.utils.utils import codegen

def double(t):
    return Call("double", Int(), t)

def target_lang():
    x = Var("x", Int())
    double = FnDeclRecursive(
        "double", Int(), Add(x, x), x
    )
    return [double]

def inv_grammar(v: Var, writes: List[Var], reads: List[Var]) -> Expr:
    raise Exception("no invariant")

def ps_grammar(ret_val: Var, writes: List[Var], reads: List[Var]) -> Expr:
    r = writes[0]
    (x, y) = reads
    summary = Choose(
        Eq(ret_val, Add(double(x), double(y))),
        Eq(ret_val, Sub(double(x), double(y))),
    )
    return summary

if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        llvm_filepath="tests/llvm/tuples3.ll",
        loops_filepath="tests/llvm/tuples3.loops",
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