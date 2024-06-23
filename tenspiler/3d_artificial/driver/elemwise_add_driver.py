from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int, Object, Tensor3D
from metalift.vc_util import and_objects
from tenspiler.tenspiler_common import (
    call_elemwise_add,
    matrix_elemwise_add,
    tensor3d_elemwise_add,
    vec_elemwise_add,
)


def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [tensor3d_elemwise_add, matrix_elemwise_add, vec_elemwise_add]


def inv0_grammar_fn(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    result, i, j, k, lst, matrix, _ = writes
    a, b = reads
    return and_objects(i >= 0, i <= a.len(), result == call_elemwise_add(a[:i], b[:i]))


def inv1_grammar_fn(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    j, k, lst, matrix, _ = writes
    a, b = reads
    result, i = in_scope
    return and_objects(
        i >= 0,
        i < a.len(),
        j >= 0,
        j <= a[0].len(),
        matrix == call_elemwise_add(a[i][:j], b[i][i:j]),
        result == call_elemwise_add(a[:i], b[:i]),
    )


def inv2_grammar_fn(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    k, lst, _ = writes
    a, b = reads
    result, i, matrix, j = in_scope
    return and_objects(
        i >= 0,
        i < a.len(),
        j >= 0,
        j < a[0].len(),
        k >= 0,
        k <= a[0][0].len(),
        lst == call_elemwise_add(a[i][j][:k], a[i][j][:k]),
        matrix == call_elemwise_add(a[i][:j], b[i][:j]),
        result == call_elemwise_add(a[:i], b[:i]),
    )


def ps_grammar_fn(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    result = writes[0]
    a, b = reads
    return result == call_elemwise_add(a, b)


if __name__ == "__main__":
    driver = Driver()
    inv0_grammar = InvGrammar(inv0_grammar_fn, [])
    inv1_grammar = InvGrammar(inv1_grammar_fn, ["i", "agg.result"])
    inv2_grammar = InvGrammar(inv2_grammar_fn, ["i", "agg.result", "j", "matrix"])
    elemwise_add = driver.analyze(
        llvm_filepath="tenspiler/3d_artificial/cpp/elemwise_add.ll",
        loops_filepath="tenspiler/3d_artificial/cpp/elemwise_add.loops",
        fn_name="elemwise_add",
        target_lang_fn=target_lang,
        inv_grammars={
            "elemwise_add_inv0": inv0_grammar,
            "elemwise_add_inv1": inv1_grammar,
            "elemwise_add_inv2": inv2_grammar,
        },
        ps_grammar=ps_grammar_fn,
    )
    tensor3d_x = Tensor3D(Int, "tensor3d_x")
    tensor3d_y = Tensor3D(Int, "tensor3d_y")
    driver.add_var_objects([tensor3d_x, tensor3d_y])

    # Add preconditions
    driver.add_precondition(tensor3d_x.len() > 1)
    driver.add_precondition(tensor3d_x.len() == tensor3d_y.len())
    driver.add_precondition(tensor3d_x[0].len() > 1)
    driver.add_precondition(tensor3d_x[0].len() == tensor3d_y[0].len())
    driver.add_precondition(tensor3d_x[0][0].len() > 1)
    driver.add_precondition(tensor3d_x[0][0].len() == tensor3d_y[0][0].len())
    elemwise_add(tensor3d_x, tensor3d_y)
    driver.synthesize(
        filename="elemwise_add", list_bound=2, relaxed_grammar=False, rounds_to_guess=0
    )
