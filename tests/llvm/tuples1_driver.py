from typing import List, Literal

from metalift.frontend.llvm import Driver
from metalift.ir import (Add, Call, Choose, Eq, Expr, FnDeclRecursive,
                         IntObject, Mul, Sub, Tuple, TupleObject, Var)
from tests.python.utils.utils import codegen


def tuple_mult(t):
    return Call("tuple_mult", IntObject, t)

def target_lang():
    x = TupleObject[IntObject, Literal[2]](IntObject, Literal[2], "x")
    tuple_mult = FnDeclRecursive(
        "tuple_mult",
        IntObject,
        Mul(x[0], x[1]), # TODO(jie): maybe we can even rewrite this mul using *
        x
    )
    return [tuple_mult]

def inv_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    raise Exception("no invariant!")

def ps_grammar(ret_val: Var, writes: List[Var], reads: List[Var]) -> Expr:
    (x, y) = reads
    x_tuple_src = Tuple(x, x)
    y_tuple_src = Tuple(y, y)
    x_tuple = TupleObject[IntObject, Literal[2]](IntObject, Literal[2], x_tuple_src)
    y_tuple = TupleObject[IntObject, Literal[2]](IntObject, Literal[2], y_tuple_src)
    summary = Choose(
        Eq(ret_val, Add(tuple_mult(x_tuple), tuple_mult(y_tuple))),
        Eq(ret_val, Sub(tuple_mult(x_tuple), tuple_mult(y_tuple))),
    )
    return summary

if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        llvm_filepath="tests/llvm/tuples1.ll",
        loops_filepath="tests/llvm/tuples1.loops",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammars=defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar=ps_grammar
    )

    x = IntObject("x")
    y = IntObject("y")
    driver.add_var_objects([x, y])

    test(x, y)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))