from typing import List, Union
from metalift.frontend.llvm import Driver
from metalift.ir import BoolObject, FnDecl, FnDeclRecursive, IntObject, ListObject, NewObject
from metalift.vc_util import and_objects
from tests.python.utils.utils import codegen
from tests.llvm.gaudi.gaudi_common import elemwise_mul, nested_elemwise_max, call_elemwise_max, call_nested_elemwise_max

def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [elemwise_mul, nested_elemwise_max]

def ps_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> BoolObject:
    ret_val = writes[0]
    base, active = reads
    return ret_val == call_nested_elemwise_max(base, active)

def inv0_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> BoolObject:
    # outer loop grammar
    # TODO: figure out which one is row
    # TODO: investigate why row_vec appeared twice
    out, row_vec, _, col, row = writes
    base, active = reads
    return and_objects(
        row >= 0,
        row < base.len(),
        out == call_nested_elemwise_max(base[:row], active[:row])
    )

def inv1_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> BoolObject:
    # inner loop grammar
    import pdb; pdb.set_trace()
    row, col, tmp, out = writes
    base, active = reads
    return and_objects(
        row >= 0,
        row < base.len(),
        col >= 0,
        col <= base[0].len(),
        tmp == call_elemwise_max(base[row][:col], active[row][:col]),
    )
    pass
if __name__ == "__main__":
    driver = Driver()
    darken_blend_8 = driver.analyze(
        llvm_filepath="tests/llvm/gaudi/darken_blend_8.ll",
        loops_filepath="tests/llvm/gaudi/darken_blend_8.loops",
        fn_name="darken_blend_8",
        target_lang_fn=target_lang,
        inv_grammars={
            "darken_blend_8_inv0": inv0_grammar,
            "darken_blend_8_inv1": inv1_grammar
        },
        ps_grammar=ps_grammar
    )

    base = ListObject(ListObject[IntObject], "base")
    active = ListObject(ListObject[IntObject], "active")
    driver.add_var_objects([base, active])
    driver.add_precondition(base.len() > 1)
    driver.add_precondition(base.len() == active.len())
    driver.add_precondition(base[0].len() == active[0].len())

    darken_blend_8(base, active)

    driver.synthesize(noVerify=True)

    print("\n\ngenerated code:" + darken_blend_8.codegen(codegen))
