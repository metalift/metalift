from typing import List

from metalift.frontend.python import Driver
from metalift.ir import Bool, FnDeclRecursive, Int, Object, call, fn_decl_recursive
from tests.python.utils.utils import codegen

UNINTERP_FN_NAME = "uninterp"


def uninterp(x: Object, y: Object) -> Object:
    return call(UNINTERP_FN_NAME, Int, x, y)


def target_lang() -> List[FnDeclRecursive]:
    x = Int("x")
    y = Int("y")
    uninterp = fn_decl_recursive(UNINTERP_FN_NAME, Int, None, x, y)
    return [uninterp]


def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    ret_val = writes[0]
    x, y = reads
    return ret_val == uninterp(x, x) + uninterp(y, y)


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    raise Exception("no loop in the source")


if __name__ == "__main__":
    filename = "tests/python/uninterp.py"
    uninterp_fns = [UNINTERP_FN_NAME]

    driver = Driver()
    driver.uninterp_fns = uninterp_fns
    test = driver.analyze(
        filename,
        "test",
        target_lang,
        inv_grammar,
        ps_grammar,
        uninterp_fns=uninterp_fns,
    )

    i = Int("i")
    j = Int("j")
    driver.add_var_objects([i, j])

    test(i, j)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))
