from collections import defaultdict
from typing import List

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int, Object
from metalift.ir import Tuple as mlTuple
from metalift.ir import call, choose, ite, make_tuple, make_tuple_type
from tests.python.utils.utils import codegen

L1_NORM = "l1_norm"
MAT_MUL = "mat_mul"
TWO_INT_TUPLE_TYPE = make_tuple_type(Int, Int)


def target_lang() -> List[FnDeclRecursive]:
    a = mlTuple((Int, Int), "a")
    b = mlTuple((Int, Int), "b")
    x = mlTuple((Int, Int), "x")
    p0l = a[0] * x[0]
    p0r = b[0] * x[1]
    p1l = a[1] * x[0]
    p1r = b[1] * x[1]
    mat_mul_body = make_tuple(p0l + p0r, p1l + p1r)
    mat_mul = FnDecl(MAT_MUL, TWO_INT_TUPLE_TYPE, mat_mul_body.src, a.src, b.src, x.src)

    p = mlTuple((Int, Int), "p")
    p0 = p[0]
    p1 = p[1]
    p0_abs = ite(p0 < 0, 0 - p0, p0)
    p1_abs = ite(p1 < 0, 0 - p1, p1)
    l1_norm_body = p0_abs + p1_abs
    l1_norm = FnDecl(L1_NORM, Int, l1_norm_body.src, p.src)

    return [mat_mul, l1_norm]


def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    ret_val = writes[0]
    a0, a1, b0, b1, x0, x1 = reads
    # Calculate the matrix-vector product
    a = make_tuple(a0, a1)
    b = make_tuple(b0, b1)
    x = make_tuple(x0, x1)
    p = call(MAT_MUL, TWO_INT_TUPLE_TYPE, a, b, x)
    wrong_p = call(MAT_MUL, TWO_INT_TUPLE_TYPE, b, a, x)
    wrong_p2 = call(MAT_MUL, TWO_INT_TUPLE_TYPE, a, x, b)

    # this is the correct answer
    l1_norm_p = call(L1_NORM, Int, p)
    # this is a wrong answer
    l1_norm_wrong_p = call(L1_NORM, Int, wrong_p)
    # this is a wrong answer
    l1_norm_wrong_p2 = call(L1_NORM, Int, wrong_p2)

    return ret_val == choose(l1_norm_p, l1_norm_wrong_p, l1_norm_wrong_p2)


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    raise Exception("no loop in the source")


if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        llvm_filepath="tests/llvm/no_loop_matmul.ll",
        loops_filepath="tests/llvm/no_loop_matmul.loops",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammars=defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar=ps_grammar,
    )

    a0 = Int("a0")
    a1 = Int("a1")
    b0 = Int("b0")
    b1 = Int("b1")
    x0 = Int("x0")
    x1 = Int("x1")
    driver.add_var_objects([a0, a1, b0, b1, x0, x1])

    test(a0, a1, b0, b1, x0, x1)

    driver.synthesize(filename="no_loop_matmul")

    print("\n\ngenerated code:" + test.codegen(codegen))
