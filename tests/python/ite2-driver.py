from typing import List
from metalift.frontend.python import Driver

from metalift.ir import (
    Eq,
    Expr,
    FnDecl,
    Int,
    IntLit,
    Ite,
    Var,
)

from mypy.nodes import Statement


def target_lang() -> List[FnDecl]:
    return []


def ps_grammar(
    ret_val: Var,
    ast: Statement,
    writes: List[Var],
    reads: List[Var],
    in_scope: List[Var],
) -> Expr:
    i = reads[0]
    default = IntLit(40)
    case3 = Ite(Eq(i, IntLit(3)), IntLit(30), default)
    case2 = Ite(Eq(i, IntLit(2)), IntLit(20), case3)
    case1 = Ite(Eq(i, IntLit(1)), IntLit(10), case2)
    return Eq(ret_val, case1)


def inv_grammar(
    v: Var, ast: Statement, writes: List[Var], reads: List[Var], in_scope: List[Var]
) -> Expr:
    raise Exception("no loop in the source")


if __name__ == "__main__":
    filename = "tests/python/ite2.py"

    driver = Driver()
    test = driver.analyze(filename, "test", target_lang, inv_grammar, ps_grammar)

    arg = driver.variable("arg", Int())
    test(arg)

    driver.synthesize()
