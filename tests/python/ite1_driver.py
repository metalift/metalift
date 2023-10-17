from typing import List

from metalift.frontend.python import Driver

from metalift.ir import (
    Eq,
    Expr,
    FnDecl,
    IntObject,
    Ite,
    NewObject,
)


def target_lang() -> List[FnDecl]:
    return []


def ps_grammar(
    ret_val: NewObject,
    writes: List[NewObject],
    reads: List[NewObject],
    in_scope: List[NewObject],
) -> Expr:
    i = reads[0]
    return Eq(ret_val, Ite(i > 10, IntObject(1), IntObject(2)))


def inv_grammar(
    v: NewObject, writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]
) -> Expr:
    raise Exception("no loop in the source")


if __name__ == "__main__":
    filename = "tests/python/ite1.py"

    driver = Driver()
    test = driver.analyze(filename, "test", target_lang, inv_grammar, ps_grammar)

    i = IntObject("i")
    driver.add_var_object(i)
    test(i)

    driver.synthesize()
