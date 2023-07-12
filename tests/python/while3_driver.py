from typing import List

from mypy.nodes import Statement

from metalift.frontend.python import Driver
from metalift.ir import (Add, And, BoolLit, Call, Choose, Eq, Expr, FnDeclRecursive, Ge, Gt,
                         Int, IntLit, Ite, Le, Lt, Or, Sub, Var)
from tests.python.utils.utils import codegen


def target_lang() -> List[FnDeclRecursive]:
    x = Var("x", Int())
    sum_n = FnDeclRecursive(
        "sum_n",
        Int(),
        Ite(
            Ge(x, IntLit(1)), Add(x, Call("sum_n", Int(), Sub(x, IntLit(1)))), IntLit(0)
        ),
        x,
    )
    return [sum_n]


def ps_grammar(ret_val: Var, ast: Statement, writes: List[Var], reads: List[Var], in_scope: List[Var]) -> Expr:
    # input_arg = reads[0]
    choices = Choose(IntLit(1), IntLit(2), IntLit(3))
    # cond = Ite(
    #     Eq(IntLit(0), reads[0]),
    #     IntLit(0),
    #     Call("sum_n", Int(), Sub(reads[0], choices))
    # )
    # return Eq(ret_val, cond)
    # b = Or(Ge(IntLit(1), reads[0]), Eq(ret_val, Call("sum_n", Int(), Sub(reads[0], choices))))
    int_lit = Choose(IntLit(0), IntLit(1), IntLit(2))
    input_arg_cond = Lt(reads[0], IntLit(1))
    ite_stmt = Ite(
        Lt(reads[0], IntLit(1)),
        IntLit(0),
        Call("sum_n", Int(), Sub(reads[0], choices))
    )
    # b = Or(input_arg_cond, Eq(ret_val, Call("sum_n", Int(), Sub(reads[0], choices))))
    b = Eq(ret_val, ite_stmt)
    # b = ite_stmt
    return b

def inv_grammar(v: Var, ast: Statement, writes: List[Var], reads: List[Var], in_scope: List[Var]) -> Expr:
    if v.name() != "x":
        return BoolLit(True)
    x, y = writes
    input_arg = reads[0]
    int_lit = Choose(IntLit(0), IntLit(1), IntLit(2))
    x_or_y = Choose(x, y)
    x_or_y_int_lit_bound = Choose(
        Ge(x_or_y, int_lit),
        Le(x_or_y, int_lit),
        Gt(x_or_y, int_lit),
        Lt(x_or_y, int_lit),
        Eq(x_or_y, int_lit),
    )
    x_or_y_input_arg_bound = Choose(
        Ge(x_or_y, input_arg),
        Le(x_or_y, input_arg),
        Gt(x_or_y, input_arg),
        Lt(x_or_y, input_arg),
        Eq(x_or_y, input_arg),
    )
    input_arg_bound = Ge(input_arg, int_lit)
    inv_cond = And(
        input_arg_bound,
        And(
            x_or_y_int_lit_bound,
            And(
                x_or_y_input_arg_bound,
                Eq(x, Call("sum_n", Int(), Sub(y, int_lit)))
            ),
        )
    )
    # inv_cond = And(
    #     y_bound_arg_cond,
    #     Eq(x, Call("sum_n", Int(), Sub(y, int_lit)))
    # )
    # return Choose(inv_cond)
    input_arg_cond = Lt(reads[0], IntLit(1))
    x_cond = Eq(x, IntLit(0))
    y_cond = Eq(y, IntLit(1))

    # b = Or(inv_cond, And(y_bound_invalid_cond, x_cond))
    b = Or(inv_cond, input_arg_cond)
    b = Or(inv_cond, And(input_arg_cond, And(x_cond, y_cond)))
    # input_arg <= 1 and y > input_arg
    # b = Or(inv_cond, And(input_arg_cond, y_bound_invalid_cond))
    return b

if __name__ == "__main__":
    filename = "tests/python/while3.py"

    driver = Driver()
    test = driver.analyze(filename, "test", target_lang, inv_grammar, ps_grammar)

    v1 = driver.variable("input_arg", Int())

    test(v1)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))
