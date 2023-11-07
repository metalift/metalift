from typing import List, Union
from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import BoolObject, FnDecl, FnDeclRecursive, IntObject, ListObject, NewObject
from metalift.vc_util import and_objects
from tests.python.utils.utils import codegen
from tests.llvm.gaudi.gaudi_common import get_select_synth, nested_selection, selection, call_nested_selection, select_fn_obj, call_selection, select_fn_decl, select_mul8x8_div255_body

def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    # return [elemwise_min, nested_elemwise_min]
    return [select_fn_decl, selection, nested_selection]

def ps_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> BoolObject:
    ret_val = writes[0]
    base, active = reads
    return ret_val == call_nested_selection(base, active, select_fn_obj)

def inv0_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> BoolObject:
    # outer loop grammar
    out, _, _, row, _ = writes
    base, active = reads
    return and_objects(
        row >= 0,
        row <= base.len(),
        out == call_nested_selection(base[:row], active[:row], select_fn_obj)
    )

def inv1_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> BoolObject:
    # inner loop grammar
    col, _, row_vec = writes
    row = in_scope[0]
    base, active = reads
    return and_objects(
        row >= 0,
        row < base.len(),
        col >= 0,
        col <= base[0].len(),
        row_vec == call_selection(base[row][:col], active[row][:col], select_fn_obj),
    )

if __name__ == "__main__":
    driver = Driver()
    multiply_blend_8 = driver.analyze(
        llvm_filepath="tests/llvm/gaudi/multiply_blend_8.ll",
        loops_filepath="tests/llvm/gaudi/multiply_blend_8.loops",
        fn_name="multiply_blend_8",
        target_lang_fn=target_lang,
        inv_grammars={
            "multiply_blend_8_inv0": InvGrammar(inv0_grammar, []),
            "multiply_blend_8_inv1": InvGrammar(inv1_grammar, ["row"])
        },
        ps_grammar=ps_grammar
    )

    base = ListObject(ListObject[IntObject], "base")
    active = ListObject(ListObject[IntObject], "active")
    driver.add_var_objects([base, active])
    driver.add_precondition(base.len() > 1)
    driver.add_precondition(base.len() == active.len())
    driver.add_precondition(base[0].len() == active[0].len())
    driver.fns_synths = [get_select_synth(select_mul8x8_div255_body)]
    multiply_blend_8(base, active)

    driver.synthesize(noVerify=True)

    print("\n\ngenerated code:" + multiply_blend_8.codegen(codegen))
