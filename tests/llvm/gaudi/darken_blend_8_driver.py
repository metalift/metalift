import time

from metalift.frontend.llvm import Driver
from metalift.ir import Int, Matrix
from tests.llvm.gaudi.gaudi_common import (
    get_select_two_args_synth_without_analysis,
    selection_two_args_inv0_grammar, selection_two_args_inv1_grammar,
    selection_two_args_ps_grammar_fn, selection_two_args_target_lang)
from tests.python.utils.utils import codegen
from tests.llvm.gaudi.gaudi_common import get_select_synth, nested_selection, select_min_body, selection, call_nested_selection, select_fn_obj, call_selection, select_fn_decl

def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    # return [elemwise_min, nested_elemwise_min]
    return [select_fn_decl, selection, nested_selection]

def ps_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    ret_val = writes[0]
    base, active = reads
    return ret_val == call_nested_selection(base, active, select_fn_obj)

def inv0_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    # outer loop grammar
    out, col, row, row_vec = writes
    base, active = reads
    return and_objects(
        row >= 0,
        row <= base.len(),
        out == call_nested_selection(base[:row], active[:row], select_fn_obj)
    )

def inv1_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    # inner loop grammar
    col, row_vec = writes
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
    darken_blend_8 = driver.analyze(
        llvm_filepath="tests/llvm/gaudi/darken_blend_8.ll",
        loops_filepath="tests/llvm/gaudi/darken_blend_8.loops",
        fn_name="darken_blend_8",
        target_lang_fn=selection_two_args_target_lang,
        inv_grammars={
            "darken_blend_8_inv0": selection_two_args_inv0_grammar,
            "darken_blend_8_inv1": selection_two_args_inv1_grammar
        },
        ps_grammar=selection_two_args_ps_grammar_fn
    )

    base = Matrix(Int, "base")
    active = Matrix(Int, "active")
    driver.add_var_objects([base, active])

    # Add preconditions
    driver.add_precondition(base.len() > 1)
    driver.add_precondition(base.len() == active.len())
    driver.add_precondition(base[0].len() == active[0].len())

    int_x = Int("int_x")
    int_y = Int("int_y")
    select_synth = get_select_two_args_synth_without_analysis(0)
    driver.fns_synths = [select_synth]
    darken_blend_8(base, active)

    start_time = time.time()
    driver.synthesize(listBound=3, noVerify=True)
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
    print("\n\ngenerated code:" + darken_blend_8.codegen(codegen))


