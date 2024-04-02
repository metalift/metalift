import time

from metalift.frontend.llvm import Driver
from metalift.ir import Int, Matrix
from tenspiler.tenspiler_common import get_matrix_select_general_search_space
from tests.python.utils.utils import codegen

if __name__ == "__main__":
    driver = Driver()
    (
        inv0_grammar,
        inv1_grammar,
        ps_grammar_fn,
        target_lang,
        fns_synths,
    ) = get_matrix_select_general_search_space(
        driver=driver, depth=4, cons=[Int(2), Int(16), Int(32)]
    )
    overlay_blend_8 = driver.analyze(
        llvm_filepath="tenspiler/dexter/cpp/for_synthesis/overlay_blend_8.ll",
        loops_filepath="tenspiler/dexter/cpp/for_synthesis/overlay_blend_8.loops",
        fn_name="overlay_blend_8",
        target_lang_fn=target_lang,
        inv_grammars={
            "overlay_blend_8_inv0": inv0_grammar,
            "overlay_blend_8_inv1": inv1_grammar,
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
    overlay_blend_8(base, active)

    start_time = time.time()
    driver.synthesize(filename="overlay_blend_8", rounds_to_guess=0)
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
    print("\n\ngenerated code:" + overlay_blend_8.codegen(codegen))
