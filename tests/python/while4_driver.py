from typing import List

from metalift.frontend.python import Driver
from metalift.ir import (FnDeclRecursive, IntObject, NewObject, call, choose,
                         ite, fnDeclRecursive)
from tests.python.utils.utils import codegen


def target_lang() -> List[FnDeclRecursive]:
    x = IntObject("x")
    sum_n = fnDeclRecursive(
        "sum_n",
        IntObject,
        ite(
            x >= 1,
            x + call("sum_n", IntObject, x - 1),
            IntObject(0),
        ),
        x
    )
    return [sum_n]


def ps_grammar(ret_val: NewObject, writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> NewObject:
    return ret_val == call("sum_n", IntObject, choose(IntObject(1), IntObject(2)))

def inv_grammar(v: NewObject, writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> NewObject:
    e = choose(*writes)
    f = choose(IntObject(1), IntObject(2), IntObject(3))
    c = e == call("sum_n", IntObject, e - f)
    d = (e >= f).And(e <= f)
    b = c.And(d)
    return b

if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        filepath="tests/python/while4.py",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammar=inv_grammar,
        ps_grammar=ps_grammar
    )

    test()

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))