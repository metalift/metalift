from typing import List
from metalift.frontend.python import Driver

from metalift.ir import (
    Add,
    Call,
    Eq,
    Expr,
    FnDecl,
    Gt,
    Int,
    IntLit,
    Ite,
    Var,
)

from mypy.nodes import Statement


def target_lang() -> List[FnDecl]:
    x = Var("x", Int())
    y = Var("y", Int())
    my_add = FnDecl("my_add", Int(), Add(x, y), x, y)
    return [my_add]


def ps_grammar(
    ret_val: Var,
    ast: Statement,
    writes: List[Var],
    reads: List[Var],
    in_scope: List[Var],
) -> Expr:
    x, y = reads
    return Eq(ret_val, Call("my_add", Int(), x, y))


def inv_grammar(
    v: Var, ast: Statement, writes: List[Var], reads: List[Var], in_scope: List[Var]
) -> Expr:
    raise Exception("no loop in the source")


if __name__ == "__main__":
    filename = "tests/python/class1.py"

    driver = Driver()
    test = driver.analyze(filename, "test", target_lang, inv_grammar, ps_grammar)

    f1 = driver.variable("f1", Int())
    f2 = driver.variable("f2", Int())
    test(f1, f2)

    driver.synthesize()
