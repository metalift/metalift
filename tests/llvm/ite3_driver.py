from typing import List

from metalift.frontend.llvm import Driver
from metalift.ir import Eq, Expr, FnDecl, IntObject, Ite, NewObject


def target_lang() -> List[FnDecl]:
    return []


def ps_grammar(ret_val: NewObject, writes: List[NewObject], reads: List[NewObject]) -> Expr:
    i = reads[0]
    return Eq(ret_val, Ite(i > 10, IntObject(2), IntObject(1)))


def inv_grammar(v: NewObject, writes: List[NewObject], reads: List[NewObject]) -> Expr:
    raise Exception("no loop in the source")


if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        llvm_filepath="tests/llvm/ite3.ll",
        loops_filepath="tests/llvm/ite3.loops",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammar=inv_grammar,
        ps_grammar=ps_grammar
    )

    i = IntObject("i")
    driver.add_var_object(i)
    test(i)

    driver.synthesize()
