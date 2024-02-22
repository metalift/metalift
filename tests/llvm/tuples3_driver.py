from collections import defaultdict
from typing import List

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Int, Object, call, choose, fn_decl_recursive
from tests.python.utils.utils import codegen


def double(t):
    return call("double", Int, t)


def target_lang():
    x = Int("x")
    double = fn_decl_recursive("double", Int, (x + x), x)
    return [double]


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Object:
    raise Exception("no invariant")


def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Object:
    ret_val = writes[0]
    (x, y) = reads
    summary = choose(ret_val == double(x) + double(y), ret_val == double(x) - double(y))
    return summary


if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        llvm_filepath="tests/llvm/tuples3.ll",
        loops_filepath="tests/llvm/tuples3.loops",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammars=defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar=ps_grammar,
    )

    x = Int("x")
    y = Int("y")
    driver.add_var_objects([x, y])

    test(x, y)

    driver.synthesize(filename="tuples3")
    print("\n\ngenerated code:" + test.codegen(codegen))
