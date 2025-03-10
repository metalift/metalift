from typing import List

from metalift.frontend.python import Driver
from metalift.ir import (Bool, FnDeclRecursive, Int, Object,
                         call, choose, ite, fn_decl_recursive)
from tests.python.utils.utils import codegen


def target_lang() -> List[FnDeclRecursive]:
    x = Int("x")
    add_n = fn_decl_recursive(
        "add_n",
        Int,
        ite(
            x >= 1,
            1 + call("add_n", Int, x - 1),
            Int(0)
        ),
        x,
    )
    return [add_n]

def ps_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    ret_val = writes[0]
    int_lit = choose(Int(0), Int(1), Int(2), Int(3), Int(4), Int(5))
    return ret_val == call("add_n", Int, int_lit)

def inv_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    x = writes[0]
    y = reads[1]
    int_lit = choose(Int(0), Int(1), Int(2), Int(3), Int(4), y)
    bound = choose(
        x <= int_lit,
        x >= int_lit,
        x > int_lit,
        x < int_lit,
        x == int_lit
    )
    return bound.And(bound)


if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        filepath="tests/python/usecase2.py",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammar=inv_grammar,
        ps_grammar=ps_grammar
    )

    test()

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))