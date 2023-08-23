from typing import List
from metalift.frontend.python import Driver

from metalift.ir import Add, Call, Choose, Eq, Expr, FnDecl, Int, IntLit, Sub, Tuple, TupleGet, TupleT, Var

from mypy.nodes import Statement

from tests.python.utils.utils import codegen

def target_lang() -> List[FnDecl]:
    x = Var("x", TupleT(Int(), Int()))
    tuple_add = FnDecl(
        "tuple_add", 
        Int(), 
        Add(TupleGet(x, IntLit(0)), TupleGet(x, IntLit(1))),
        x
    )
    return [tuple_add]

def ps_grammar(ret_val: Var, ast: Statement, writes: List[Var], reads: List[Var], in_scope: List[Var]) -> Expr:
    def tuple_add(t: Expr):
        return Call("tuple_add", Int(), t)
    x, y = reads[0], reads[1]
    return Choose(
        Eq(ret_val, Add(tuple_add(Tuple(x, x)), tuple_add(Tuple(y, y)))),
        Eq(ret_val, Sub(tuple_add(Tuple(x, x)), tuple_add(Tuple(y, y)))),
    )

def inv_grammar(v: Var, ast: Statement, writes: List[Var], reads: List[Var], in_scope: List[Var]) -> Expr:
    raise Exception("no invariant")
    
if __name__ == "__main__":
    filename = "tests/python/tuples2.py"

    driver = Driver()    
    test = driver.analyze(filename, "test", target_lang, inv_grammar, ps_grammar)

    v1 = driver.variable("x", Int())
    v2 = driver.variable("y", Int())

    test(v1, v2)
    
    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))
