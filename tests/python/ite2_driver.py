from typing import List

from metalift.frontend.python import Driver
from metalift.ir import Bool, FnDecl, Int, Object, ite


def target_lang() -> List[FnDecl]:
    return []


def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    ret_val = writes[0]
    i = reads[0]
    default = Int(40)
    case3 = ite(i == 3, Int(30), default)
    case2 = ite(i == 2, Int(20), case3)
    case1 = ite(i == 1, Int(10), case2)
    return ret_val == case1


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    raise Exception("no loop in the source")


if __name__ == "__main__":
    filename = "tests/python/ite2.py"

    driver = Driver()
    test = driver.analyze(filename, "test", target_lang, inv_grammar, ps_grammar)

    arg = Int("arg")
    driver.add_var_object(arg)
    test(arg)

    driver.synthesize()
