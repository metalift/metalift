from typing import List

from metalift.frontend.python import Driver
from metalift.ir import Bool, FnDecl, Int, Object, call, choose, fn_decl
from metalift.vc_util import and_objects
from tests.python.utils.utils import codegen


def target_lang() -> List[FnDecl]:
    x = Int("x")
    y = Int("y")
    z = Int("z")
    fma = fn_decl("fma", Int, (x + y * z), x, y, z)
    return [fma]


# var := *reads | 0
# added := var + var
# var_or_fma := *reads | fma(added, added, added)
#
# return value := var_or_fma + var_or_fma
#
def ps_grammar(
    writes: List[Object],
    reads: List[Object],
    in_scope: List[Object],
) -> Bool:
    ret_val = writes[0]
    var = choose(*reads, Int(0))
    added = var + var
    var_or_fma = choose(*reads, call("fma", Int, added, added, added))

    return ret_val == var_or_fma + var_or_fma


# invariant: i <= arg2 and p = arg1 * i
def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    (arg1, arg2, i, p) = reads

    value = choose(arg1, arg2, arg1 * i, arg2 * i)
    return and_objects(choose(i <= value, i == value), choose(p <= value, p == value))


if __name__ == "__main__":
    filename = "tests/python/fma2.py"

    driver = Driver()
    test = driver.analyze(filename, "test", target_lang, inv_grammar, ps_grammar)

    base1 = Int("base1")
    arg1 = Int("arg1")
    base2 = Int("base2")
    arg2 = Int("arg2")
    driver.add_var_objects([base1, arg1, base2, arg2])

    driver.add_precondition(arg2 >= 0)

    test(base1, arg1, base2, arg2)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))
