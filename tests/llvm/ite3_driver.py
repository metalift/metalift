from collections import defaultdict
from typing import List

from metalift.frontend.llvm import Driver
from metalift.ir import Eq, Expr, FnDecl, Gt, IntObject, Ite, Var


def target_lang() -> List[FnDecl]:
    return []


def ps_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    ret_val = writes[0]
    i = reads[0]
    return Eq(ret_val, Ite(Gt(i, IntObject(10)), IntObject(2), IntObject(1)))


def inv_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    raise Exception("no loop in the source")


if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        llvm_filepath="tests/llvm/ite3.ll",
        loops_filepath="tests/llvm/ite3.loops",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammars=defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar=ps_grammar
    )

    i = IntObject("i")
    driver.add_var_object(i)
    test(i)

    driver.synthesize()
