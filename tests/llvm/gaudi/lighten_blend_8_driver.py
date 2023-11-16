import time

from metalift.frontend.llvm import Driver
from metalift.ir import Int, List as mlList
from tests.llvm.gaudi.gaudi_common import (get_select_two_args_synth, select_lighten_blend_body, selection_two_args_inv0_grammar,
                                           selection_two_args_inv1_grammar,
                                           selection_two_args_ps_grammar_fn,
                                           selection_two_args_synth,
                                           select_two_args_general_synth,
                                           selection_two_args_target_lang)
from tests.python.utils.utils import codegen

if __name__ == "__main__":
    driver = Driver()
    lighten_blend_8 = driver.analyze(
        llvm_filepath="tests/llvm/gaudi/lighten_blend_8.ll",
        loops_filepath="tests/llvm/gaudi/lighten_blend_8.loops",
        fn_name="lighten_blend_8",
        target_lang_fn=selection_two_args_target_lang,
        inv_grammars={
            "lighten_blend_8_inv0": selection_two_args_inv0_grammar,
            "lighten_blend_8_inv1": selection_two_args_inv1_grammar
        },
        ps_grammar=selection_two_args_ps_grammar_fn
    )

    base = mlList(mlList[Int], "base")
    active = mlList(mlList[Int], "active")
    driver.add_var_objects([base, active])

    # Add preconditions
    driver.add_precondition(base.len() > 1)
    driver.add_precondition(base.len() == active.len())
    driver.add_precondition(base[0].len() == active[0].len())

    int_x = Int("x")
    int_y = Int("y")
    driver.fns_synths = [
        get_select_two_args_synth([select_lighten_blend_body(int_x, int_y)], [int_x, int_y]), selection_two_args_synth
    ]
    lighten_blend_8(base, active)

    start_time = time.time()
    driver.synthesize(listBound=3, noVerify=True)
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
    print("\n\ngenerated code:" + lighten_blend_8.codegen(codegen))
