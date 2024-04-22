import time

from metalift.frontend.llvm import Driver
from metalift.ir import Int, Matrix
from tenspiler.codegen.utils import DataType
from tenspiler.tenspiler_common import (
    darken_blend_8_hole_body,
    get_matrix_select_holing_search_space,
)
from tenspiler.utils.synthesis_utils import run_synthesize_algorithm

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
        llvm_filepath="tenspiler/blend/cpp/for_synthesis/darken_blend_8.ll",
        loops_filepath="tenspiler/blend/cpp/for_synthesis/darken_blend_8.loops",
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
    run_synthesize_algorithm(
        driver=driver,
        data_type=DataType.UINT_8,
        benchmark_name="darken_blend_8",
        list_bound_start=2,
        has_relaxed=False,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
