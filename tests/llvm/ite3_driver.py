from collections import defaultdict
from typing import List

from metalift.frontend.llvm import Driver
from metalift.ir import BoolObject, FnDecl, IntObject, NewObject, ite


def target_lang() -> List[FnDecl]:
    return []


def ps_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> BoolObject:
    ret_val = writes[0]
    i = reads[0]
    return ret_val == ite(i > 10, IntObject(2), IntObject(1))


def inv_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> BoolObject:
    raise Exception("no loop in the source")


if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        llvm_filepath="tests/llvm/ite3.ll",
        loops_filepath="tests/llvm/ite3.loops",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammars=defaultdict(lambda: inv_grammar),
        ps_grammar=ps_grammar
    )

    i = IntObject("i")
    driver.add_var_object(i)
    test(i)

    driver.synthesize()
