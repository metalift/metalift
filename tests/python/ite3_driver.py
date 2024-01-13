from typing import List

from metalift.frontend.python import Driver
from metalift.ir import Bool, FnDecl, Int, Object, ite


def target_lang() -> List[FnDecl]:
    return []


def ps_grammar(
    writes: List[Object],
    reads: List[Object],
    in_scope: List[Object],
) -> Bool:
    ret_val = writes[0]
    i = reads[0]
    return ret_val == ite(i > 10, Int(2), Int(1))


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    raise Exception("no loop in the source")


if __name__ == "__main__":
    filename = "tests/python/ite3.py"

    driver = Driver()
    test = driver.analyze(filename, "test", target_lang, inv_grammar, ps_grammar)

    i = Int("i")
    driver.add_var_object(i)
    test(i)

    driver.synthesize()
