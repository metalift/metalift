import time
from collections import OrderedDict

from metalift.frontend.llvm import Driver
from metalift.ir import Int, Matrix, synth
from tests.llvm.gaudi.gaudi_common import (
    FIXED_SELECT_TWO_ARGS, get_multi_depth_with_counts_select_general_synth,
    select_color_burn_body, selection_two_args_inv0_grammar,
    selection_two_args_inv1_grammar, selection_two_args_ps_grammar_fn,
    selection_two_args_target_lang)
from tests.python.utils.utils import codegen

if __name__ == "__main__":
    driver = Driver()
    color_burn_8 = driver.analyze(
        llvm_filepath="tests/llvm/gaudi/color_burn_8.ll",
        loops_filepath="tests/llvm/gaudi/color_burn_8.loops",
        fn_name="color_burn_8",
        target_lang_fn=selection_two_args_target_lang,
        inv_grammars={
            "color_burn_8_inv0": selection_two_args_inv0_grammar,
            "color_burn_8_inv1": selection_two_args_inv1_grammar
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
    ordered_compute_ops = OrderedDict()
    ordered_compute_ops["-"] = 2
    ordered_compute_ops["//"] = 1
    select_synth = get_multi_depth_with_counts_select_general_synth(
        args=[int_x, int_y],
        constants=[Int(0), Int(32)],
        ordered_compute_ops=ordered_compute_ops,
        compare_ops=["=="],
        cond_lhs_depth=0,
        cond_rhs_depth=0,
        if_then_depth=0,
        if_else_depth=3
    )
    fixed_select_synth = synth(
        FIXED_SELECT_TWO_ARGS,
        select_color_burn_body(int_x, int_y),
        int_x,
        int_y
    )
    driver.fns_synths = [select_synth, fixed_select_synth]
    color_burn_8(base, active)

    start_time = time.time()
    driver.synthesize(listBound=2, noVerify=True)
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
    print("\n\ngenerated code:" + color_burn_8.codegen(codegen))
