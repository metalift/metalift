from collections import defaultdict
from typing import List

from metalift.frontend.llvm import Driver
from metalift.ir import (Add, Call, Choose, Eq, Expr, FnDecl, Int,
                         FnDeclRecursive, IntLit, IntObject, Mul, Sub, Tuple, TupleGet, TupleT, Var)
from tests.python.utils.utils import codegen

def double(t):
    return IntObject(Call("double", IntObject, t))

def target_lang():
    x = IntObject("x")
    double = FnDeclRecursive(
        "double",
        IntObject,
        x + x,
        x
    )
    return [double]

def inv_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Object:
    raise Exception("no invariant")

def ps_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Object:
    ret_val = writes[0]
    (x, y) = reads
    summary = Choose(
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