from typing import List

from metalift.frontend.python import Driver
from metalift.ir import BoolObject, FnDecl, IntObject, NewObject, ite


def target_lang() -> List[FnDecl]:
    return []


def ps_grammar(ret_val: NewObject, writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> BoolObject:
    ret_val = writes[0]
    i = reads[0]
    default = IntObject(40)
    case3 = ite(i == 3, IntObject(30), default)
    case2 = ite(i == 2, IntObject(20), case3)
    case1 = ite(i == 1, IntObject(10), case2)
    return ret_val == case1


def inv_grammar(v: NewObject, writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> BoolObject:
    raise Exception("no loop in the source")


if __name__ == "__main__":
    filename = "tests/python/ite2.py"

    driver = Driver()
    test = driver.analyze(filename, "test", target_lang, inv_grammar, ps_grammar)

    arg = IntObject("arg")
    driver.add_var_object(arg)
    test(arg)

    driver.synthesize()
