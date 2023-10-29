from typing import List

from metalift.frontend.python import Driver
from metalift.ir import (Call, Choose, Expr,
                         FnDeclRecursive, IntObject, NewObject, call)
from tests.python.utils.utils import codegen

def double(t):
    return IntObject(call("double", IntObject, t))

def target_lang():
    x = IntObject("x")
    double = FnDeclRecursive(
        "double",
        IntObject,
        x + x,
        x
    )
    return [double]

def inv_grammar(v: NewObject, writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> Expr:
    raise Exception("no invariant")

def ps_grammar(ret_val: NewObject, writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> Expr:
    r = writes[0]
    (x, y) = reads
    summary = Choose(
        ret_val == double(x) + double(y),
        ret_val == double(x) - double(y)
    )
    return summary

if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        filepath="tests/python/tuples3.py",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammar=inv_grammar,
        ps_grammar=ps_grammar
    )

    x = IntObject("x")
    y = IntObject("y")
    driver.add_var_objects([x, y])

    test(x, y)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))