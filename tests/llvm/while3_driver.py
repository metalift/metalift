from typing import List

from metalift.frontend.llvm import Driver
from metalift.ir import (Add, And, BoolLit, Call, Choose, Eq, Expr,
                         FnDeclRecursive, Ge, Gt, Int, IntLit, Ite, Le, Lt, Or,
                         Sub, Var)
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


def ps_grammar(ret_val: Var, writes: List[Var], reads: List[Var]) -> Expr:
    input_arg = reads[0]
    int_lit = Choose(IntLit(0), IntLit(1), IntLit(2))
    input_arg_bound = Choose(
        Ge(input_arg, int_lit),
        Le(input_arg, int_lit),
        Gt(input_arg, int_lit),
        Lt(input_arg, int_lit),
        Eq(input_arg, int_lit),
    )
    ite_stmt = Ite(
        input_arg_bound,
        IntLit(0),
        Call("sum_n", Int(), Sub(reads[0], int_lit))
    )
    return Eq(ret_val, ite_stmt)

def inv_grammar(v: Var, writes: List[Var], reads: List[Var]) -> Expr:
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
    input_arg_bound = Choose(
        Ge(input_arg, int_lit),
        Le(input_arg, int_lit),
        Gt(input_arg, int_lit),
        Lt(input_arg, int_lit),
        Eq(input_arg, int_lit),
    )

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
    not_in_loop_cond = And(
        input_arg_bound,
        And(
            Eq(x, int_lit),
            Eq(y, int_lit)
        )
    )

    return Or(inv_cond, not_in_loop_cond)

if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        llvm_filepath="tests/llvm/while3.ll",
        loops_filepath="tests/llvm/while3.loops",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammar=inv_grammar,
        ps_grammar=ps_grammar
    )

    arg = driver.variable("arg", Int())
    test(arg)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))