from typing import List
from metalift.frontend.python import Driver

from metalift.ir import Add, And, BoolLit, Call, Choose, Eq, Expr, FnDecl, FnDeclRecursive, Ge, Int, IntLit, Ite, Le, Lit, Or, Sub, Var

from mypy.nodes import Statement, WhileStmt

from tests.python.utils.utils import codegen


def target_lang() -> List[FnDeclRecursive]:
    x = Var("x", Int())
    sum_n = FnDeclRecursive(
        "sum_n",
        Int(),
        Ite(
            Ge(x, IntLit(1)),
            Add(x, Call("sum_n", Int(), Sub(x, IntLit(1)))),
            IntLit(0)
        ),
        x,
    )
    return [sum_n]

def ps_grammar(ret_val: Var, ast: Statement, writes: List[Var], reads: List[Var], in_scope: List[Var]) -> Expr:
    # writes = [test_rv]
    # reads = [input_arg]
    input_arg = reads[0]
    import pdb; pdb.set_trace()
    int_lit = Choose(IntLit(0), IntLit(1), IntLit(2), IntLit(3))
    return Eq(
        ret_val,
        Ite(
            Ge(int_lit, input_arg),
            int_lit,
            Call("sum_n", Int(), Sub(input_arg, int_lit))
        )
    )

def inv_grammar(v: Var, ast: Statement, writes: List[Var], reads: List[Var], in_scope: List[Var]) -> Expr:
    if v.name() != "x":
        return BoolLit(True)

    # writes = [x, y]
    # reads = [input_arg, x, y]
    input_arg, x, y = reads
    int_lit = Choose(IntLit(0), IntLit(1), IntLit(2))
    choose_x_y = Choose(*reads)
    inv_cond = And(
        Ge(choose_x_y, IntLit(1)),
        And(
            Le(choose_x_y, input_arg),
            Eq(choose_x_y, Call("sum_n", Int(), Sub(choose_x_y, int_lit)))
        ),
    )
    input_arg_bound = Choose(Ge(IntLit(1), input_arg), Le(IntLit(1), input_arg))
    return Or(input_arg_bound, inv_cond)

if __name__ == "__main__":
    filename = "tests/python/while3.py"

    driver = Driver()
    test = driver.analyze(filename, "test", target_lang, inv_grammar, ps_grammar)

    v1 = driver.variable("input_arg", Int())

    test(v1)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))
