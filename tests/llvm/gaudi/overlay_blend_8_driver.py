import time

from metalift.frontend.llvm import Driver
from metalift.ir import Int, Matrix, synth
from tests.llvm.gaudi.gaudi_common import (FIXED_SELECT_TWO_ARGS,
                                           get_select_two_args_general_synth,
                                           select_overlay_blend_body,
                                           selection_two_args_inv0_grammar,
                                           selection_two_args_inv1_grammar,
                                           selection_two_args_ps_grammar_fn,
                                           selection_two_args_target_lang)
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
    select_synth = get_select_two_args_general_synth(
        args=[int_x, int_y],
        constants=[Int(2), Int(128), Int(255)],
        compute_ops=["+", "-", "*", "//"],
        compare_ops=[">="],
        depth=5
    )
    fixed_select_synth = synth(
        FIXED_SELECT_TWO_ARGS,
        select_overlay_blend_body(int_x, int_y),
        int_x,
        int_y
    )
    driver.fns_synths = [select_synth, fixed_select_synth]
    overlay_blend_8(base, active)

    start_time = time.time()
    driver.synthesize(listBound=2, noVerify=True)
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
    print("\n\ngenerated code:" + overlay_blend_8.codegen(codegen))
