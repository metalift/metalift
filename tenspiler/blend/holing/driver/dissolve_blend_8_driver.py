import time

from metalift.frontend.llvm import Driver
from metalift.ir import Int, Matrix
from tenspiler.axioms import dissolve_matrix_selection_two_args_axiom
from tenspiler.codegen.utils import DataType
from tenspiler.tenspiler_common import get_dissolve_holing_search_space
from tenspiler.utils.synthesis_utils import run_synthesis_algorithm

if __name__ == "__main__":
    driver = Driver()
    (
        inv0_grammar,
        inv1_grammar,
        ps_grammar_fn,
        target_lang,
        fns_synths,
    ) = get_dissolve_holing_search_space(driver)

    def target_lang_axiom():
        return target_lang() + [dissolve_matrix_selection_two_args_axiom]

    dissolve_blend_8 = driver.analyze(
        llvm_filepath="tenspiler/blend/cpp/for_synthesis/dissolve_blend_8.ll",
        loops_filepath="tenspiler/blend/cpp/for_synthesis/dissolve_blend_8.loops",
        fn_name="dissolve_blend_8",
        target_lang_fn=target_lang_axiom,
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

    start_time = time.time()
    dissolve_blend_8(base, active, opacity, rand_cons)
    run_synthesis_algorithm(
        driver=driver,
        data_type=DataType.FLOAT,
        benchmark_name="dissovle_blend_8",
        has_relaxed=False,
    )
    end_time = time.time()

    print(f"Synthesis took {end_time - start_time} seconds")
