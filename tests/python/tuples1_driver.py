from typing import List

from metalift.frontend.python import Driver
from metalift.ir import (BoolObject, IntObject, TupleObject, NewObject, call, choose, fn_decl_recursive, make_tuple)
from tests.python.utils.utils import codegen


def tuple_mult(t):
    return call("tuple_mult", IntObject, t)

def target_lang():
    x = TupleObject((IntObject, IntObject), "x")
    tuple_mult = fn_decl_recursive(
        "tuple_mult",
        IntObject,
        x[0] * x[1],
        x
    )
    return [tuple_mult]

def inv_grammar(v: NewObject, writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> BoolObject:
    raise Exception("no invariant")

def ps_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> BoolObject:
    ret_val = writes[0]
    x_tuple = make_tuple(x, x)
    y_tuple = make_tuple(y, y)
    summary = choose(
        ret_val == tuple_mult(x_tuple) + tuple_mult(y_tuple),
        ret_val == tuple_mult(x_tuple) - tuple_mult(y_tuple)
    )
    return summary

if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        filepath="tests/python/tuples1.py",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammar=inv_grammar,
        ps_grammar=ps_grammar
    )

    x = IntObject("x")
    y = IntObject("y")
    driver.add_var_objects([x, y])

    test(x, y)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))