from collections import OrderedDict
import time

from metalift.frontend.llvm import Driver
from metalift.ir import Int, Matrix, synth
from tests.llvm.gaudi.gaudi_common import (
    FIXED_SELECT_TWO_ARGS,
    get_multi_depth_select_general_synth,
    get_multi_depth_with_counts_and_constants_select_general_synth,
    get_multi_depth_with_counts_select_general_synth,
    get_select_two_args_synth_without_analysis,
    select_overlay_blend_body,
    selection_two_args_inv0_grammar, selection_two_args_inv1_grammar,
    selection_two_args_ps_grammar_fn, selection_two_args_target_lang)
from tests.python.utils.utils import codegen

if __name__ == "__main__":
    driver = Driver()
    overlay_blend_8 = driver.analyze(
        llvm_filepath="tests/llvm/gaudi/overlay_blend_8.ll",
        loops_filepath="tests/llvm/gaudi/overlay_blend_8.loops",
        fn_name="overlay_blend_8",
        target_lang_fn=selection_two_args_target_lang,
        inv_grammars={
            "overlay_blend_8_inv0": selection_two_args_inv0_grammar,
            "overlay_blend_8_inv1": selection_two_args_inv1_grammar
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
    if_then_ordered_compute_ops = OrderedDict({
        (2 * int_x, "+", None): 1,
        (None, "-", None): 1,
        (None, "-", 32): 1,
        (2 * int_x, "*", None): 1,
        (None, "//", 32): 1
    })
    if_else_ordered_compute_ops = OrderedDict({
        (2 * int_x, "*", None): 1,
        (None, "//", 32): 1
    })
    select_synth = get_multi_depth_with_counts_and_constants_select_general_synth(
        args=[int_x, int_y],
        constants=[Int(16)],
        compare_ops=[">="],
        cond_lhs_depth=0,
        cond_rhs_depth=0,
        if_then_depth=3,
        if_else_depth=2,
        cond_lhs_ordered_compute_ops=OrderedDict(),
        cond_rhs_ordered_compute_ops=OrderedDict(),
        if_then_ordered_compute_ops=if_then_ordered_compute_ops,
        if_else_ordered_compute_ops=if_else_ordered_compute_ops
    )
    fixed_select_synth = synth(
        FIXED_SELECT_TWO_ARGS,
        select_overlay_blend_body(int_x, int_y),
        int_x,
        int_y
    )
    driver.fns_synths = [select_synth]
    overlay_blend_8(base, active)

    start_time = time.time()
    driver.synthesize(listBound=2, noVerify=True)
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
    print("\n\ngenerated code:" + overlay_blend_8.codegen(codegen))
