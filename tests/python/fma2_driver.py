from typing import List
from metalift.frontend.python import Driver

from metalift.ir import (
    Add,
    Call,
    Choose,
    Eq,
    Expr,
    FnDecl,
    Ge,
    Int,
    IntLit,
    Le,
    Lit,
    Var,
)

from mypy.nodes import Statement, WhileStmt

from tests.python.utils.utils import codegen


def target_lang() -> List[FnDecl]:
    x = Var("x", Int())
    y = Var("y", Int())
    z = Var("z", Int())
    fma = FnDecl("fma", Int(), x + y * z, x, y, z)
    return [fma]


# var := *reads | 0
# added := var + var
# var_or_fma := *reads | fma(added, added, added)
#
# return value := var_or_fma + var_or_fma
#
def ps_grammar(
    ret_val: Var,
    ast: Statement,
    writes: List[Var],
    reads: List[Var],
    in_scope: List[Var],
) -> Expr:
    var = Choose(*reads, IntLit(0))
    added = var + var
    var_or_fma = Choose(*reads, Call("fma", Int(), added, added, added))

    return Eq(ret_val, var_or_fma + var_or_fma)


# invariant: i <= arg2 and p = arg1 * i
def inv_grammar(
    v: Var, o: Statement, writes: List[Var], reads: List[Var], in_scope: List[Var]
) -> Expr:
    (arg1, arg2, i, p) = reads

    value = Choose(arg1, arg2, arg1 * i, arg2 * i)
    return Choose(Le(v, value), Eq(v, value))


if __name__ == "__main__":
    filename = "tests/python/fma2.py"

    driver = Driver()
    test = driver.analyze(filename, "test", target_lang, inv_grammar, ps_grammar)

    v1 = driver.variable("base", Int())
    v2 = driver.variable("arg1", Int())
    v3 = driver.variable("base2", Int())
    v4 = driver.variable("arg2", Int())

    driver.add_precondition(Ge(v4, IntLit(0)))

    test(v1, v2, v3, v4)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))
