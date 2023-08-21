from typing import List

from metalift.frontend.llvm import Driver
from metalift.ir import Eq, Expr, FnDecl, Gt, Int, IntLit, Ite, Var


def target_lang() -> List[FnDecl]:
    return []


def ps_grammar(ret_val: Var, writes: List[Var], reads: List[Var]) -> Expr:
    i = reads[0]
    return Eq(ret_val, Ite(Gt(i, IntLit(10)), IntLit(1), IntLit(2)))


def inv_grammar(v: Var, writes: List[Var], reads: List[Var]) -> Expr:
    raise Exception("no loop in the source")


if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        llvm_filepath="tests/llvm/ite1.ll",
        loops_filepath="tests/llvm/ite1.loops",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammar=inv_grammar,
        ps_grammar=ps_grammar
    )

    i = driver.variable("i", Int())
    test(i)

    driver.synthesize()
