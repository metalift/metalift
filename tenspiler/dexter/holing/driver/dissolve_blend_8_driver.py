import time

from metalift.frontend.llvm import Driver
from metalift.ir import Int, Matrix
from tenspiler.tenspiler_common import get_dissolve_holing_search_space

if __name__ == "__main__":
    driver = Driver()
    (
        inv0_grammar,
        inv1_grammar,
        ps_grammar_fn,
        target_lang,
        fns_synths,
    ) = get_dissolve_holing_search_space(driver)
    dissolve_blend_8 = driver.analyze(
        llvm_filepath="tenspiler/dexter/cpp/for_synthesis/dissolve_blend_8.ll",
        loops_filepath="tenspiler/dexter/cpp/for_synthesis/dissolve_blend_8.loops",
        fn_name="dissolve_blend_8",
        target_lang_fn=target_lang,
        inv_grammars={
            "dissolve_blend_8_inv0": inv0_grammar,
            "dissolve_blend_8_inv1": inv1_grammar,
        },
        ps_grammar=ps_grammar_fn,
    )

    base = Matrix(Int, "base")
    active = Matrix(Int, "active")
    opacity = Int("opacity")
    rand_cons = Int("rand_cons")
    driver.add_var_objects([base, active, opacity, rand_cons])

    # Add preconditions
    driver.add_precondition(base.len() > 1)
    driver.add_precondition(base.len() == active.len())
    driver.add_precondition(base[0].len() == active[0].len())

    driver.fns_synths = fns_synths
    dissolve_blend_8(base, active, opacity, rand_cons)

    start_time = time.time()
    driver.synthesize(filename="dissolve_blend_8", rounds_to_guess=0, no_verify=True)

    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
