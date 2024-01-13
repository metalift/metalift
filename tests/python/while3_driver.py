from typing import List

from metalift.frontend.python import Driver
from metalift.ir import (
    Bool,
    FnDeclRecursive,
    Int,
    Object,
    call,
    choose,
    fn_decl_recursive,
    ite,
)
from metalift.vc_util import and_objects
from tests.python.utils.utils import codegen


def target_lang() -> List[FnDeclRecursive]:
    x = Int("x")
    sum_n = fn_decl_recursive(
        "sum_n",
        Int,
        ite(x >= 1, x + call("sum_n", Int, x - 1), Int(0)),
        x,
    )
    return [sum_n]


def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    ret_val = writes[0]
    input_arg = reads[0]
    int_lit = choose(Int(0), Int(1), Int(2))
    input_arg_bound = choose(
        input_arg >= int_lit,
        input_arg <= int_lit,
        input_arg > int_lit,
        input_arg < int_lit,
        input_arg == int_lit,
    )
    ite_stmt = ite(input_arg_bound, Int(0), call("sum_n", Int, reads[0] - int_lit))
    return ret_val == ite_stmt


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    x, y = writes
    input_arg = reads[0]
    int_lit = choose(Int(0), Int(1), Int(2))
    x_or_y = choose(x, y)
    x_or_y_int_lit_bound = choose(
        x_or_y >= int_lit,
        x_or_y <= int_lit,
        x_or_y > int_lit,
        x_or_y < int_lit,
        x_or_y == int_lit,
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
        x == call("sum_n", Int, y - int_lit),
    )

    not_in_loop_cond = and_objects(input_arg_bound, x == int_lit, y == int_lit)
    return inv_cond.Or(not_in_loop_cond)


if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        filepath="tests/python/while3.py",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammar=inv_grammar,
        ps_grammar=ps_grammar,
    )

    input_arg = Int("input_arg")
    driver.add_var_object(input_arg)
    test(input_arg)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))
