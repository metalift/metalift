from typing import List

from mypy.nodes import Statement

from metalift.frontend.python import Driver
from metalift.ir import (Add, Call, Choose, Eq, Expr, FnDecl, FnDeclRecursive,
                         Int, IntLit, Ite, Lt, Mul, Sub, Tuple, TupleGet,
                         TupleT, Var)
from tests.python.utils.utils import codegen

UNINTERP_FN_NAME = "uninterp"

def uninterp(x: Var, y: Var):
    return Call(UNINTERP_FN_NAME, Int(), x, y)

def target_lang() -> List[FnDeclRecursive]:
    x = Var("x", Int())
    y = Var("y", Int())
    uninterp = FnDeclRecursive(UNINTERP_FN_NAME, Int(), None, x, y)
    return [uninterp]


def ps_grammar(ret_val: Var, ast: Statement, writes: List[Var], reads: List[Var], in_scope: List[Var]) -> Expr:
    x, y = reads
    return Eq(ret_val, Add(uninterp(x, x), uninterp(y, y)))

def inv_grammar(v: Var, ast: Statement, writes: List[Var], reads: List[Var], in_scope: List[Var]) -> Expr:
    raise Exception("no loop in the source")

if __name__ == "__main__":
    filename = "tests/python/uninterp.py"

    driver = Driver()
    test = driver.analyze(filename, "test", target_lang, inv_grammar, ps_grammar, uninterp_fns=["uninterp"])

    i = driver.variable("i", Int())
    j = driver.variable("j", Int())

    test(i, j)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))
