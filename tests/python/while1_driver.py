from typing import List
from metalift.frontend.python import Driver

from metalift.ir import Eq, Expr, FnDecl, Int, IntLit, Ite, Le, Var
from mypy.nodes import WhileStmt

import sys

# ps: y = ite(y<=x, x, 0)
def ps_grammar(
    ret_val: Var,
    ast: WhileStmt,
    writes: List[Var],
    reads: List[Var],
    in_scope: List[Var],
) -> Expr:
    x = reads[0]
    return Eq(ret_val, Ite(Le(IntLit(0), x), x, IntLit(0)))


# inv: ite(y<=x, y<=x, y=0)
def inv_grammar(
    v: Var, o: WhileStmt, writes: List[Var], reads: List[Var], in_scope: List[Var]
) -> Expr:
    return Ite(Le(v, reads[0]), Le(IntLit(0), reads[0]), Eq(v, IntLit(0)))


def target() -> List[FnDecl]:
    return []


if __name__ == "__main__":
    filename = "tests/python/while1.py" if len(sys.argv) == 1 else sys.argv[1]

    driver = Driver()
    test = driver.analyze(filename, "test", target, inv_grammar, ps_grammar)

    i = driver.variable("i", Int())
    r = test(i)

    driver.synthesize()
    # no codegen
