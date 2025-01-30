from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int, Object, Tensor3D, choose
from metalift.vc_util import and_objects
from tenspiler.tenspiler_common import (
    call_elemwise_add,
    call_elemwise_mul,
    matrix_elemwise_add,
    matrix_elemwise_mul,
    tensor3d_elemwise_add,
    tensor3d_elemwise_mul,
    vec_elemwise_add,
    vec_elemwise_mul,
)


def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        tensor3d_elemwise_add,
        matrix_elemwise_add,
        vec_elemwise_add,
        tensor3d_elemwise_mul,
        matrix_elemwise_mul,
        vec_elemwise_mul,
    ]


def inv0_grammar_fn(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    result, i, j, k, lst, matrix, _ = writes
    tensor3d_x, tensor3d_y = reads
    tensor3d = choose(tensor3d_x, tensor3d_y)
    return and_objects(
        i >= 0,
        i <= tensor3d_x.len(),
        result
        == call_elemwise_add(
            tensor3d[:i],
            call_elemwise_mul(
                call_elemwise_add(tensor3d[:i], tensor3d[:i]), tensor3d[:i]
            ),
        ),
    )


def inv1_grammar_fn(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    j, k, lst, matrix, _ = writes
    tensor3d_x, tensor3d_y = reads
    tensor3d = choose(tensor3d_x, tensor3d_y)
    result, i = in_scope
    return and_objects(
        i >= 0,
        i < tensor3d_x.len(),
        j >= 0,
        j <= tensor3d_x[0].len(),
        matrix
        == call_elemwise_add(
            tensor3d[i][:j],
            call_elemwise_mul(
                call_elemwise_add(tensor3d[i][:j], tensor3d[i][:j]), tensor3d[i][:j]
            ),
        ),
        result
        == call_elemwise_add(
            tensor3d[:i],
            call_elemwise_mul(
                call_elemwise_add(tensor3d[:i], tensor3d[:i]), tensor3d[:i]
            ),
        ),
    )


def inv2_grammar_fn(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    k, lst, _ = writes
    tensor3d_x, tensor3d_y = reads
    tensor3d = choose(tensor3d_x, tensor3d_y)
    result, i, matrix, j = in_scope
    return and_objects(
        i >= 0,
        i < tensor3d_x.len(),
        j >= 0,
        j < tensor3d_x[0].len(),
        k >= 0,
        k <= tensor3d_x[0][0].len(),
        lst
        == call_elemwise_add(
            tensor3d[i][j][:k],
            call_elemwise_mul(
                call_elemwise_add(tensor3d[i][j][:k], tensor3d[i][j][:k]),
                tensor3d[i][j][:k],
            ),
        ),
        matrix
        == call_elemwise_add(
            tensor3d[i][:j],
            call_elemwise_mul(
                call_elemwise_add(tensor3d[i][:j], tensor3d[i][:j]), tensor3d[i][:j]
            ),
        ),
        result
        == call_elemwise_add(
            tensor3d[:i],
            call_elemwise_mul(
                call_elemwise_add(tensor3d[:i], tensor3d[:i]), tensor3d[:i]
            ),
        ),
    )


def ps_grammar_fn(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    result = writes[0]
    tensor3d_x, tensor3d_y = reads
    tensor3d = choose(tensor3d_x, tensor3d_y)
    return result == call_elemwise_add(
        tensor3d,
        call_elemwise_mul(call_elemwise_add(tensor3d, tensor3d), tensor3d),
    )


if __name__ == "__main__":
    driver = Driver()
    inv0_grammar = InvGrammar(inv0_grammar_fn, [])
    inv1_grammar = InvGrammar(inv1_grammar_fn, ["i", "agg.result"])
    inv2_grammar = InvGrammar(inv2_grammar_fn, ["i", "agg.result", "j", "matrix"])
    elemwise_depth4 = driver.analyze(
        llvm_filepath="tenspiler/3d_artificial/cpp/elemwise_depth4.ll",
        loops_filepath="tenspiler/3d_artificial/cpp/elemwise_depth4.loops",
        fn_name="elemwise_depth4",
        target_lang_fn=target_lang,
        inv_grammars={
            "elemwise_depth4_inv0": inv0_grammar,
            "elemwise_depth4_inv1": inv1_grammar,
            "elemwise_depth4_inv2": inv2_grammar,
        },
        ps_grammar=ps_grammar_fn,
    )
    tensor3d_x = Tensor3D(Int, "tensor3d_x")
    tensor3d_y = Tensor3D(Int, "tensor3d_y")
    driver.add_var_objects([tensor3d_x, tensor3d_y])

    # Add preconditions
    driver.add_precondition(tensor3d_x.len() > 0)
    driver.add_precondition(tensor3d_x.len() == tensor3d_y.len())
    driver.add_precondition(tensor3d_x[0].len() > 0)
    driver.add_precondition(tensor3d_x[0].len() == tensor3d_y[0].len())
    driver.add_precondition(tensor3d_x[0][0].len() > 0)
    driver.add_precondition(tensor3d_x[0][0].len() == tensor3d_y[0][0].len())
    elemwise_depth4(tensor3d_x, tensor3d_y)
    driver.synthesize(
        filename="elemwise_depth4",
        list_bound=2,
        relaxed=False,
        rounds_to_guess=0,
        no_verify=True,
    )
