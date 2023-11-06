from typing import List

from metalift.frontend.python import Driver
from metalift.ir import BoolObject, FnDecl, IntObject, NewObject, call, choose, fn_decl
from metalift.vc_util import and_objects
from tests.python.utils.utils import codegen


def target_lang() -> List[FnDecl]:
    x = IntObject("x")
    y = IntObject("y")
    z = IntObject("z")
    fma = fn_decl("fma", IntObject, (x + y * z), x, y, z)
    return [fma]


# var := *reads | 0
# added := var + var
# var_or_fma := *reads | fma(added, added, added)
#
# return value := var_or_fma + var_or_fma
#
def ps_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject],) -> BoolObject:
    ret_val = writes[0]
    var = choose(*reads, IntObject(0))
    added = var + var
    var_or_fma = choose(*reads, call("fma", IntObject, added, added, added))

    return ret_val == var_or_fma + var_or_fma


# invariant: i <= arg2 and p = arg1 * i
def inv_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> BoolObject:
    (arg1, arg2, i, p) = reads

    value = choose(arg1, arg2, arg1 * i, arg2 * i)
    return and_objects(
        choose(i <= value, i == value),
        choose(p <= value, p == value)
    )



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
