from typing import List

from metalift.frontend.python import Driver
from metalift.ir import Bool, Int, Object, call, choose, fn_decl_recursive
from tests.python.utils.utils import codegen


def double(t):
    return call("double", Int, t)


def target_lang():
    x = Int("x")
    double = fn_decl_recursive("double", Int, (x + x), x)
    return [double]


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    raise Exception("no invariant")


def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    ret_val = writes[0]
    (x, y) = reads
    summary = choose(ret_val == double(x) + double(y), ret_val == double(x) - double(y))
    return summary


if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        filepath="tests/python/tuples3.py",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammar=inv_grammar,
        ps_grammar=ps_grammar,
    )

    x = Int("x")
    y = Int("y")
    driver.add_var_objects([x, y])

    test(x, y)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))
