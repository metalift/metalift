from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int, Object, Tensor3D
from tenspiler.tenspiler_common import (
    matrix_elemwise_add,
    tensor3d_elemwise_add,
    vec_elemwise_add,
)


def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [tensor3d_elemwise_add, matrix_elemwise_add, vec_elemwise_add]


def inv0_grammar_fn(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    print("INV 0")
    import pdb

    pdb.set_trace()


def inv1_grammar_fn(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    print("INV 1")
    import pdb

    pdb.set_trace()


def ps_grammar_fn(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    print("PS")
    import pdb

    pdb.set_trace()


if __name__ == "__main__":
    driver = Driver()
    print("MADE DRIVER")
    inv0_grammar = InvGrammar(inv0_grammar_fn, [])
    inv1_grammar = InvGrammar(inv1_grammar_fn, [])
    print("MADE GRAMMAR")
    elemwise_add = driver.analyze(
        llvm_filepath="tenspiler/3d_artificial/cpp/elemwise_add.ll",
        loops_filepath="tenspiler/3d_artificial/cpp/elemwise_add.loops",
        fn_name="elemwise_add",
        target_lang_fn=target_lang,
        inv_grammars={
            "elemwise_add_inv0": inv0_grammar,
            "elemwise_add_inv1": inv1_grammar,
        },
        ps_grammar=ps_grammar_fn,
    )
    print("ANALYZED")
    a = Tensor3D(Int, "a")
    b = Tensor3D(Int, "b")
    driver.add_var_objects([a, b])

    # Add preconditions
    driver.add_precondition(a.len() > 1)
    driver.add_precondition(a.len() == b.len())
    driver.add_precondition(a[0].len() > 1)
    driver.add_precondition(a[0].len() == b[0].len())
    driver.add_precondition(a[0][0].len() > 1)
    driver.add_precondition(a[0][0].len() == b[0][0].len())
    print("HAHAHAH")
    elemwise_add(a, b)
    # driver.synthesize(
    #     filename="elemwise_add",
    #     list_bound=2,
    #     relaxed_grammar=False,
    #     rounds_to_guess=1
    # )
