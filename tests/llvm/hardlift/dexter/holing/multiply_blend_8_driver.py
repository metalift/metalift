import time

from metalift.frontend.llvm import Driver
from metalift.ir import Int, Matrix
from tests.llvm.hardlift.hardlift_common import (darken_blend_hole_body, get_matrix_computation_holing_search_space,
                                           get_select_synth_from_hole, multiply_blend_8_hole_body,
                                           selection_two_args_inv0_grammar,
                                           selection_two_args_inv1_grammar,
                                           selection_two_args_ps_grammar_fn,
                                           selection_two_args_target_lang)
from tests.python.utils.utils import codegen

if __name__ == "__main__":
    driver = Driver()
    inv0_grammar, inv1_grammar, ps_grammar_fn, target_lang, fns_synths = get_matrix_computation_holing_search_space(multiply_blend_8_hole_body)
    multiply_blend_8 = driver.analyze(
        llvm_filepath="tests/llvm/gaudi/dexter/cpp/multiply_blend_8.ll",
        loops_filepath="tests/llvm/gaudi/dexter/cpp/multiply_blend_8.loops",
        fn_name="multiply_blend_8",
        target_lang_fn=target_lang,
        inv_grammars={
            "multiply_blend_8_inv0": inv0_grammar,
            "multiply_blend_8_inv1": inv1_grammar
        },
        ps_grammar=ps_grammar_fn
    )

    base = Matrix(Int, "base")
    active = Matrix(Int, "active")
    driver.add_var_objects([base, active])

    # Add preconditions
    driver.add_precondition(base.len() > 1)
    driver.add_precondition(base.len() == active.len())
    driver.add_precondition(base[0].len() == active[0].len())

    driver.fns_synths = fns_synths
    multiply_blend_8(base, active)

    start_time = time.time()
    driver.synthesize(noVerify=True)
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
    print("\n\ngenerated code:" + multiply_blend_8.codegen(codegen))
