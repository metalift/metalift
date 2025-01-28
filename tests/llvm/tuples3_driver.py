from collections import defaultdict
from typing import List

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import IntObject, NewObject, call, choose, fn_decl_recursive
from tests.python.utils.utils import codegen

def double(t):
    return call("double", IntObject, t)

def target_lang():
    x = IntObject("x")
    double = fn_decl_recursive(
        "double",
        IntObject,
        (x + x),
        x
    )
    return [double]

def inv_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> NewObject:
    raise Exception("no invariant")

def ps_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> NewObject:
    ret_val = writes[0]
    (x, y) = reads
    summary = choose(
        ret_val == double(x) + double(y),
        ret_val == double(x) - double(y)
    )
    return summary

if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        llvm_filepath="tests/llvm/tuples3.ll",
        loops_filepath="tests/llvm/tuples3.loops",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammars=defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar=ps_grammar
    )

    x = IntObject("x")
    y = IntObject("y")
    driver.add_var_objects([x, y])

    test(x, y)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))