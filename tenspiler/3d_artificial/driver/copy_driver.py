from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int, Object, Tensor3D, choose
from metalift.vc_util import and_objects


def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return []


def inv0_grammar_fn(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    result, i, j, k, lst, matrix = writes
    tensor3d_x = reads[0]
    tensor3d = choose(tensor3d_x)
    return and_objects(
        i >= 0,
        i <= tensor3d_x.len(),
        result == tensor3d[:i],
    )


def inv1_grammar_fn(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    j, k, lst, matrix = writes
    tensor3d_x = reads[0]
    tensor3d = choose(tensor3d_x)
    result, i = in_scope
    return and_objects(
        i >= 0,
        i < tensor3d_x.len(),
        j >= 0,
        j <= tensor3d_x[0].len(),
        matrix == tensor3d[i][:j],
        result == tensor3d[:i],
    )


def inv2_grammar_fn(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    k, lst = writes
    tensor3d_x = reads[0]
    tensor3d = choose(tensor3d_x)
    result, i, matrix, j = in_scope
    return and_objects(
        i >= 0,
        i < tensor3d_x.len(),
        j >= 0,
        j < tensor3d_x[0].len(),
        k >= 0,
        k <= tensor3d_x[0][0].len(),
        lst == tensor3d[i][j][:k],
        matrix == tensor3d[i][:j],
        result == tensor3d[:i],
    )


def ps_grammar_fn(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    result = writes[0]
    tensor3d_x = reads[0]
    tensor3d = choose(tensor3d_x)
    return result == tensor3d


if __name__ == "__main__":
    driver = Driver()
    inv0_grammar = InvGrammar(inv0_grammar_fn, [])
    inv1_grammar = InvGrammar(inv1_grammar_fn, ["i", "agg.result"])
    inv2_grammar = InvGrammar(inv2_grammar_fn, ["i", "agg.result", "j", "matrix"])
    copy = driver.analyze(
        llvm_filepath="tenspiler/3d_artificial/cpp/copy.ll",
        loops_filepath="tenspiler/3d_artificial/cpp/copy.loops",
        fn_name="copy",
        target_lang_fn=target_lang,
        inv_grammars={
            "copy_inv0": inv0_grammar,
            "copy_inv1": inv1_grammar,
            "copy_inv2": inv2_grammar,
        },
        ps_grammar=ps_grammar_fn,
    )
    tensor3d_x = Tensor3D(Int, "tensor3d_x")
    driver.add_var_objects([tensor3d_x])

    # Add preconditions
    driver.add_precondition(tensor3d_x.len() > 0)
    driver.add_precondition(tensor3d_x[0].len() > 0)
    driver.add_precondition(tensor3d_x[0][0].len() > 0)
    copy(tensor3d_x)
    driver.synthesize(
        filename="copy",
        list_bound=2,
        relaxed_grammar=False,
        rounds_to_guess=0,
        no_verify=True,
    )
