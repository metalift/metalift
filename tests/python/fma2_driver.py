from typing import List
from metalift.frontend.python import Driver

from metalift.ir import (
    Call,
    Choose,
    Eq,
    Expr,
    FnDecl,
    IntObject,
    Le,
    Var,
)

from mypy.nodes import Statement, WhileStmt

from tests.python.utils.utils import codegen


def target_lang() -> List[FnDecl]:
    x = IntObject("x")
    y = IntObject("y")
    z = IntObject("z")
    fma = FnDecl("fma", IntObject, x + y * z, x, y, z)
    return [fma]


# var := *reads | 0
# added := var + var
# var_or_fma := *reads | fma(added, added, added)
#
# return value := var_or_fma + var_or_fma
#
def ps_grammar(
    ret_val: Var,
    writes: List[Var],
    reads: List[Var],
    in_scope: List[Var],
) -> Expr:
    var = Choose(*reads, IntObject(0))
    added = var + var
    var_or_fma = Choose(*reads, Call("fma", IntObject, added, added, added))

    return Eq(ret_val, var_or_fma + var_or_fma)


# invariant: i <= arg2 and p = arg1 * i
def inv_grammar(
    v: Var, writes: List[Var], reads: List[Var], in_scope: List[Var]
) -> Expr:
    (arg1, arg2, i, p) = reads

    value = Choose(arg1, arg2, arg1 * i, arg2 * i)
    return Choose(Le(v, value), Eq(v, value))


if __name__ == "__main__":
    filename = "tests/python/fma2.py"

    driver = Driver()
    test = driver.analyze(filename, "test", target_lang, inv_grammar, ps_grammar)

    base1 = IntObject("base1")
    arg1 = IntObject("arg1")
    base2 = IntObject("base2")
    arg2 = IntObject("arg2")
    driver.add_var_objects([base1, arg1, base2, arg2])

    driver.add_precondition(arg2 >= 0)

    test(base1, arg1, base2, arg2)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))
