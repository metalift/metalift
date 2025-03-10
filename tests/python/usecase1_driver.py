from typing import List

from metalift.frontend.python import Driver
from metalift.ir import (Bool, FnDeclRecursive, Int, Object,
                         call, choose, fn_decl_recursive, fn_decl, ite)
from tests.python.utils.utils import codegen


def target_lang() -> List[FnDeclRecursive]:

    x = Int("x")
    y = Int("y")
    z = Int("z")
    lan = fn_decl(
        "lan",
        Int,
        (x + y // z),
        x,y,z
    )
    return [lan]



def ps_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    ret_val = writes[0]
    var = choose(*reads, Int(0), Int(1))
    added = var + var
    call_object = call("lan", Int, added, added, added)
    var_or_call = choose(*reads, call_object)
    return ret_val == call_object + call_object

def inv_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    raise Exception("no loop in the source")

if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        filepath="tests/python/usecase1.py",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammar=inv_grammar,
        ps_grammar=ps_grammar
    )

    arg1 = Int("arg1")
    arg2 = Int("arg2")
    driver.add_var_objects([arg1, arg2])

    test(arg1, arg2)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))