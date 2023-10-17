from typing import List
from metalift.frontend.python import Driver

from metalift.ir import Eq, Expr, FnDecl, IntObject, Ite, Le, NewObject

import sys
from typing import List

from metalift.frontend.python import Driver
from metalift.ir import Bool, FnDecl, Int, Object, ite


# ps: y = ite(y<=x, x, 0)
def ps_grammar(
    ret_val: NewObject,
    writes: List[NewObject],
    reads: List[NewObject],
    in_scope: List[NewObject],
) -> Expr:
    x = reads[0]
    return Eq(ret_val, Ite(0 <= x, x, IntObject(0)))


# inv: ite(y<=x, y<=x, y=0)
def inv_grammar(
    v: NewObject, writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]
) -> Expr:
    return Ite(
        v <= reads[0],
        0 <= reads[0],
        v == 0
    )


def target() -> List[FnDecl]:
    return []


if __name__ == "__main__":
    filename = "tests/python/while1.py" if len(sys.argv) == 1 else sys.argv[1]

    driver = Driver()
    test = driver.analyze(filename, "test", target, inv_grammar, ps_grammar)

    x = IntObject("x")
    driver.add_var_object(x)
    r = test(x)

    driver.synthesize()
    # no codegen
