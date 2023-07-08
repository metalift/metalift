from typing import List

from mypy.nodes import Statement

from metalift.frontend.python import Driver
from metalift.ir import (Call, Choose, Eq, Expr, FnDecl, Int, IntLit, Ite,
                         SetT, Var)
from tests.python.utils.utils import codegen


def target_lang() -> List[FnDecl]:
    return []

def ps_grammar(ret_val: Var, ast: Statement, writes: List[Var], reads: List[Var], in_scope: List[Var]) -> Expr:
    input_s, input_add, input_value = reads
    int_lit = Choose(IntLit(0), IntLit(1), IntLit(2), IntLit(3))
    int_value = Choose(input_value, int_lit)

    condition = Eq(input_add, int_lit)

    empty_set = Call("set-create", SetT(Int()))
    set_in = Choose(input_s, empty_set, Call("set-singleton", SetT(Int()), int_value))
    set_transform = Choose(
        set_in,
        Call("set-union", SetT(Int()), set_in, set_in),
        Call("set-minus", SetT(Int()), set_in, set_in),
    )
    return Eq(ret_val, Ite(condition, set_transform, set_transform))

def inv_grammar(v: Var, ast: Statement, writes: List[Var], reads: List[Var], in_scope: List[Var]) -> Expr:
    raise Exception("no loop in the source")


if __name__ == "__main__":
    filename = "tests/python/set1.py"

    driver = Driver()
    test = driver.analyze(filename, "test", target_lang, inv_grammar, ps_grammar)

    v1 = driver.variable("s", SetT(Int()))
    v2 = driver.variable("add", Int())
    v3 = driver.variable("value", Int())

    test(v1, v2, v3)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))
