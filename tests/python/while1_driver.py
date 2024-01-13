import sys
from typing import List

from metalift.frontend.python import Driver
from metalift.ir import Bool, FnDecl, Int, Object, ite


# ps: y = ite(y<=x, x, 0)
def ps_grammar(
    writes: List[Object],
    reads: List[Object],
    in_scope: List[Object],
) -> Bool:
    ret_val = writes[0]
    x = reads[0]
    return ret_val == ite(0 <= x, x, Int(0))


# inv: ite(y<=x, 0<=x, y=0)
def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    x, y = reads
    return ite(y <= x, 0 <= x, y == 0)


def target() -> List[FnDecl]:
    return []


if __name__ == "__main__":
    filename = "tests/python/while1.py" if len(sys.argv) == 1 else sys.argv[1]

    driver = Driver()
    test = driver.analyze(filename, "test", target, inv_grammar, ps_grammar)

    x = Int("x")
    driver.add_var_object(x)
    r = test(x)

    driver.synthesize()
    # no codegen
