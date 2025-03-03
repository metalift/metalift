import time

from metalift.frontend.llvm import Driver
from metalift.ir import Int, Matrix
from metalift.utils.tenspiler.tenspiler_common import (
    get_matrix_computation_holing_search_space,
    multiply_blend_8_hole_body,
)
from tests.llvm.tenspiler.axioms import (
    matrix_elemwise_mul_axiom,
    matrix_scalar_div_axiom,
)
from tests.llvm.tenspiler.codegen.utils import DataType
from tests.llvm.tenspiler.utils.synthesis_utils import run_synthesis_algorithm

if __name__ == "__main__":
    driver = Driver()
    (
        inv0_grammar,
        inv1_grammar,
        ps_grammar_fn,
        target_lang,
        fns_synths,
    ) = get_matrix_computation_holing_search_space(multiply_blend_8_hole_body)

    def target_lang_axiom():
        return target_lang() + [matrix_scalar_div_axiom, matrix_elemwise_mul_axiom]

    multiply_blend_8 = driver.analyze(
        llvm_filepath="tests/llvm/tenspiler/multiply_blend_8.ll",
        loops_filepath="tests/llvm/tenspiler/multiply_blend_8.loops",
        fn_name="multiply_blend_8",
        target_lang_fn=target_lang_axiom,
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

    start_time = time.time()
    multiply_blend_8(base, active)
    run_synthesis_algorithm(
        driver=driver,
        data_type=DataType.UINT_8,
        benchmark_name="multiply_blend_8",
        has_relaxed=False,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
