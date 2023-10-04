from typing import List

from metalift.frontend.llvm import Driver
from metalift.ir import (Add, And, Call, Choose, Eq, Expr, FnDeclRecursive, Ge,
                         IntObject, Ite, Le, NewObject, Sub)
from tests.python.utils.utils import codegen


def target_lang() -> List[FnDeclRecursive]:
    x = IntObject("x")
    sum_n = FnDeclRecursive(
        "sum_n",
        IntObject,
        Ite(
            Ge(x, IntObject(1)),
            Add(x, Call("sum_n", IntObject, Sub(x, IntObject(1)))),
            IntObject(0),
        ),
        x,
    )
    return [sum_n]


def ps_grammar(ret_val: NewObject, writes: List[NewObject], reads: List[NewObject]) -> Expr:
    return Eq(ret_val, Call("sum_n", IntObject, Choose(IntObject(1), IntObject(2))))

def inv_grammar(v: NewObject, writes: List[NewObject], reads: List[NewObject]) -> Expr:
    e = Choose(*writes)
    f = Choose(IntObject(1), IntObject(2), IntObject(3))
    c = Eq(e, Call("sum_n", IntObject, Sub(e, f)))
    d = And(Ge(e, f), Le(e, f))
    b = And(c, d)
    return b

if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        llvm_filepath="tests/llvm/while4.ll",
        loops_filepath="tests/llvm/while4.loops",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammar=inv_grammar,
        ps_grammar=ps_grammar
    )

    test()

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))