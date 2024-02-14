import time

from metalift.frontend.llvm import Driver
from metalift.ir import Int, Matrix
from tests.llvm.hardlift.codegen.gaudi_codegen import gaudi_codegen
from tests.llvm.hardlift.hardlift_common import (
    darken_blend_8_hole_body,
    get_matrix_select_holing_search_space,
)

if __name__ == "__main__":
    driver = Driver()
    (
        inv0_grammar,
        inv1_grammar,
        ps_grammar_fn,
        target_lang,
        fns_synths,
    ) = get_matrix_select_holing_search_space(driver, darken_blend_8_hole_body)
    darken_blend_8 = driver.analyze(
        llvm_filepath="tests/llvm/hardlift/dexter/cpp/darken_blend_8.ll",
        loops_filepath="tests/llvm/hardlift/dexter/cpp/darken_blend_8.loops",
        fn_name="darken_blend_8",
        target_lang_fn=target_lang,
        inv_grammars={
            "darken_blend_8_inv0": inv0_grammar,
            "darken_blend_8_inv1": inv1_grammar,
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
    darken_blend_8(base, active)

    start_time = time.time()
    driver.synthesize(filename="darken_blend_8", rounds_to_guess=0, noVerify=True)
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
    ps_fn_decl = driver.get_ps_fn_decl()

    print("\n\ngenerated code:" + gaudi_codegen(ps_fn_decl, driver.synthesized_fns))
