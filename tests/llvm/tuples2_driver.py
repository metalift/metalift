from typing import List

from metalift.frontend.llvm import Driver
from metalift.ir import (IntObject, NewObject, TupleObject,
                         call, choose, make_tuple, fnDeclRecursive)
from tests.python.utils.utils import codegen


def tuple_add(t):
    return call("tuple_add", IntObject, t)

def target_lang():
    x = TupleObject(IntObject, IntObject, "x")
    tuple_add = fnDeclRecursive(
        "tuple_add",
        IntObject,
        (x[0] + x[1]),
        x
    )
    return [tuple_add]

def inv_grammar(v: NewObject, writes: List[NewObject], reads: List[NewObject]) -> NewObject:
    raise Exception("no invariants")

def ps_grammar(ret_val: NewObject, writes: List[NewObject], reads: List[NewObject]) -> NewObject:
    (x, y) = reads
    x_tuple = make_tuple(x, x)
    y_tuple = make_tuple(y, y)
    summary = choose(
        ret_val == tuple_add(x_tuple) + tuple_add(y_tuple),
        ret_val == tuple_add(x_tuple) - tuple_add(y_tuple)
    )
    return summary

if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        llvm_filepath="tests/llvm/tuples2.ll",
        loops_filepath="tests/llvm/tuples2.loops",
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