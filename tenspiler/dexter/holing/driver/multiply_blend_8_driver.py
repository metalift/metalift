import time

from metalift.frontend.llvm import Driver
from metalift.ir import Int, Matrix
from tenspiler.tenspiler_common import (
    get_matrix_computation_holing_search_space,
    multiply_blend_8_hole_body,
)

if __name__ == "__main__":
    driver = Driver()
    (
        inv0_grammar,
        inv1_grammar,
        ps_grammar_fn,
        target_lang,
        fns_synths,
    ) = get_matrix_computation_holing_search_space(multiply_blend_8_hole_body)
    multiply_blend_8 = driver.analyze(
        llvm_filepath="tenspiler/dexter/cpp/for_synthesis/multiply_blend_8.ll",
        loops_filepath="tenspiler/dexter/cpp/for_synthesis/multiply_blend_8.loops",
        fn_name="multiply_blend_8",
        target_lang_fn=target_lang,
        inv_grammars={
            "multiply_blend_8_inv0": inv0_grammar,
            "multiply_blend_8_inv1": inv1_grammar,
        },
        ps_grammar=ps_grammar_fn,
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
    driver.synthesize(filename="multiply_blend_8", rounds_to_guess=0, no_verify=True)
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
