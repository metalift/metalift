from typing import List, Literal

from metalift.frontend.llvm import Driver
from metalift.ir import (Add, Call, Choose, Expr,
                         FnDeclRecursive, IntObject, Tuple, TupleObject, NewObject)
from tests.python.utils.utils import codegen


def tuple_add(t):
    return IntObject(Call("tuple_add", IntObject, t))

def target_lang():
    x = TupleObject[IntObject, Literal[2]](IntObject, Literal[2], "x")
    tuple_add = FnDeclRecursive(
        "tuple_add",
        IntObject,
        x[0] + x[1],
        x
    )
    return [tuple_add]

def inv_grammar(v: NewObject, writes: List[NewObject], reads: List[NewObject]) -> Expr:
    raise Exception("no inNewObjectiant")

def ps_grammar(ret_val: NewObject, writes: List[NewObject], reads: List[NewObject]) -> Expr:
    (x, y) = reads
    x_tuple_src = Tuple(x, x)
    y_tuple_src = Tuple(y, y)
    x_tuple = TupleObject[IntObject, Literal[2]](IntObject, Literal[2], x_tuple_src)
    y_tuple = TupleObject[IntObject, Literal[2]](IntObject, Literal[2], y_tuple_src)
    summary = Choose(
        ret_val == tuple_add(x_tuple) +  tuple_add(y_tuple),
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
        inv_grammars=defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar=ps_grammar
    )

    x = IntObject("x")
    y = IntObject("y")
    driver.add_NewObject_objects([x, y])

    test(x, y)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))