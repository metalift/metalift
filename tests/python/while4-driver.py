from typing import List

from mypy.nodes import Statement

from metalift.frontend.python import Driver
from metalift.ir import (Add, And, Call, Choose, Eq, Expr, FnDeclRecursive, Ge,
                         Int, IntLit, Ite, Le, Sub, Var)
from tests.python.utils.utils import codegen


def target_lang() -> List[FnDeclRecursive]:
    x = Var("x", Int())
    sum_n = FnDeclRecursive(
        "sum_n",
        Int(),
        Ite(
            Ge(x, IntLit(1)),
            Add(x, Call("sum_n", Int(), Sub(x, IntLit(1)))),
            IntLit(0),
        ),
        x,
    )
    return [sum_n]


def ps_grammar(ret_val: Var, ast: Statement, writes: List[Var], reads: List[Var], in_scope: List[Var]) -> Expr:
    return Eq(ret_val, Call("sum_n", Int(), Choose(IntLit(1), IntLit(2))))

def inv_grammar(v: Var, ast: Statement, writes: List[Var], reads: List[Var], in_scope: List[Var]) -> Expr:
    e = Choose(*writes)
    f = Choose(IntLit(1), IntLit(2), IntLit(3))
    c = Eq(e, Call("sum_n", Int(), Sub(e, f)))
    d = And(Ge(e, f), Le(e, f))
    b = And(c, d)
    return b

if __name__ == "__main__":
    filename = "tests/python/while4.py"

    driver = Driver()
    test = driver.analyze(filename, "test", target_lang, inv_grammar, ps_grammar)

    test()

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))