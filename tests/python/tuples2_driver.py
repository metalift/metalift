from typing import List

from metalift.frontend.python import Driver
from metalift.ir import Bool, Int, Object
from metalift.ir import Tuple as mlTuple
from metalift.ir import call, choose, fn_decl, make_tuple
from tests.python.utils.utils import codegen


def tuple_add(t):
    return call("tuple_add", Int, t)


def target_lang():
    x = mlTuple((Int, Int), "x")
    tuple_add = fn_decl("tuple_add", Int, (x[0] + x[1]), x)
    return [tuple_add]


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    raise Exception("no invariant")


def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    ret_val = writes[0]
    (x, y) = reads
    x_tuple = make_tuple(x, x)
    y_tuple = make_tuple(y, y)
    summary = choose(
        ret_val == tuple_add(x_tuple) + tuple_add(y_tuple),
        ret_val == tuple_add(x_tuple) - tuple_add(y_tuple),
    )
    return summary


if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        filepath="tests/python/tuples2.py",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammar=inv_grammar,
        ps_grammar=ps_grammar,
    )

    x = Int("x")
    y = Int("y")
    driver.add_var_objects([x, y])

    test(x, y)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))
