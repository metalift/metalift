from typing import List

from metalift.frontend.python import Driver
from metalift.ir import (Add, And, BoolObject, Call, Choose, Eq, Expr,
                         FnDeclRecursive, Ge, Gt, IntObject, Ite, Le, Lt,
                         NewObject, Or, Sub)
from tests.python.utils.utils import codegen


def target_lang() -> List[FnDeclRecursive]:
    x = IntObject("x")
    sum_n = FnDeclRecursive(
        "sum_n",
        IntObject,
        Ite(
            x >= 1,
            Add(x, Call("sum_n", IntObject, Sub(x, IntObject(1)))),
            IntObject(0)
        ),
        x,
    )
    return [sum_n]


def ps_grammar(ret_val: NewObject, writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> Expr:
    input_arg = reads[0]
    int_lit = Choose(IntObject(0), IntObject(1), IntObject(2))
    input_arg_bound = Choose(
        Ge(input_arg, int_lit),
        Le(input_arg, int_lit),
        Gt(input_arg, int_lit),
        Lt(input_arg, int_lit),
        Eq(input_arg, int_lit),
    )
    ite_stmt = Ite(
        input_arg_bound,
        IntObject(0),
        Call("sum_n", IntObject, Sub(reads[0], int_lit))
    )
    return Eq(ret_val, ite_stmt)

def inv_grammar(v: NewObject, writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> Expr:
    if v.var_name() != "x":
        return BoolObject(True)
    x, y = writes
    input_arg = reads[0]
    int_lit = Choose(IntObject(0), IntObject(1), IntObject(2))
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
                Eq(x, Call("sum_n", IntObject, Sub(y, int_lit)))
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
        filepath="tests/python/while3.py",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammar=inv_grammar,
        ps_grammar=ps_grammar
    )

    input_arg = IntObject("input_arg")
    driver.add_var_object(input_arg)
    test(input_arg)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))