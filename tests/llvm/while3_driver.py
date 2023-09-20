from collections import defaultdict
from typing import List

from metalift.frontend.llvm import Driver
from metalift.ir import (Add, And, BoolLit, Call, Choose, Eq, Expr,
                         FnDeclRecursive, Ge, Gt, Int, Ite, Le, Lt, NewObject, Or,
                         Sub, Var, IntObject, BoolObject)
from tests.python.utils.utils import codegen


def target_lang() -> List[FnDeclRecursive]:
    x = IntObject("x")
    sum_n = FnDeclRecursive(
        "sum_n",
        Int(),
        Ite(
            Ge(x, IntObject(1)), Add(x, Call("sum_n", Int(), Sub(x, IntObject(1)))), IntObject(0)
        ),
        x,
    )
    return [sum_n]


def ps_grammar(ret_val: NewObject, writes: List[NewObject], reads: List[NewObject]) -> Expr:
    input_arg = reads[0]
    int_lit = Choose(IntObject(0), IntObject(1), IntObject(2))
    input_arg_bound = Choose(
        Ge(input_arg, int_lit),
        Le(input_arg, int_lit),
        Gt(input_arg, int_lit),
        Lt(input_arg, int_lit),
        Eq(input_arg, int_lit),
    )
    ite_stmt = ite(
        input_arg_bound,
        IntObject(0),
        Call("sum_n", Int(), Sub(reads[0], int_lit))
    )
    return ret_val == ite_stmt

def inv_grammar(v: NewObject, writes: List[NewObject], reads: List[NewObject]) -> Expr:
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
    x_or_y_input_arg_bound = choose(
        x_or_y >= input_arg,
        x_or_y <= input_arg,
        x_or_y > input_arg,
        x_or_y < input_arg,
        x_or_y == input_arg,
    )
    input_arg_bound = choose(
        input_arg >= int_lit,
        input_arg <= int_lit,
        input_arg > int_lit,
        input_arg < int_lit,
        input_arg == int_lit,
    )

    inv_cond = and_objects(
        input_arg_bound,
        x_or_y_int_lit_bound,
        x_or_y_input_arg_bound,
        x == call("sum_n", Int, y - int_lit)
    )

    not_in_loop_cond = and_objects(
        input_arg_bound,
        x == int_lit,
        y == int_lit
    )
    return inv_cond.Or(not_in_loop_cond)

if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        llvm_filepath="tests/llvm/while3.ll",
        loops_filepath="tests/llvm/while3.loops",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammars=defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar=ps_grammar
    )

    arg = IntObject("arg")
    driver.add_var_object(arg)
    test(arg)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))