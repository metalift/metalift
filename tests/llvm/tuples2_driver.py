from collections import defaultdict
from typing import List

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Int, Object
from metalift.ir import Tuple as mlTuple
from metalift.ir import call, choose, fn_decl_recursive, make_tuple
from tests.python.utils.utils import codegen


def tuple_add(t):
    return call("tuple_add", Int, t)


def target_lang():
    x = mlTuple((Int, Int), "x")
    tuple_add = fn_decl_recursive("tuple_add", Int, (x[0] + x[1]), x)
    return [tuple_add]


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Object:
    raise Exception("no invariants")


def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Object:
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
        llvm_filepath="tests/llvm/tuples2.ll",
        loops_filepath="tests/llvm/tuples2.loops",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammars=defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar=ps_grammar,
    )

    x = Int("x")
    y = Int("y")
    driver.add_var_objects([x, y])

    test(x, y)

    driver.synthesize(filename="tuples2")
    print("\n\ngenerated code:" + test.codegen(codegen))
