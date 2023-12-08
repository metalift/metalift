import time

from metalift.frontend.llvm import Driver
from metalift.ir import Int, Matrix
from tests.llvm.gaudi.gaudi_common import (
    get_matrix_computation_grammars_without_analysis,
    matrix_computation_target_lang)
from tests.python.utils.utils import codegen

if __name__ == "__main__":
    driver = Driver()
    inv0_grammar, inv1_grammar, ps_grammar = get_matrix_computation_grammars_without_analysis(2)
    multiply_blend_8 = driver.analyze(
        llvm_filepath="tests/llvm/gaudi/multiply_blend_8.ll",
        loops_filepath="tests/llvm/gaudi/multiply_blend_8.loops",
        fn_name="multiply_blend_8",
        target_lang_fn=matrix_computation_target_lang,
        inv_grammars={
            "multiply_blend_8_inv0": inv0_grammar,
            "multiply_blend_8_inv1": inv1_grammar
        },
        ps_grammar=ps_grammar
    )

    base = Matrix(Int, "base")
    active = Matrix(Int, "active")
    driver.add_var_objects([base, active])

    # Add preconditions
    driver.add_precondition(base.len() > 1)
    driver.add_precondition(base.len() == active.len())
    driver.add_precondition(base[0].len() == active[0].len())

    multiply_blend_8(base, active)

    start_time = time.time()
    driver.synthesize(listBound=3, noVerify=True)
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
    print("\n\ngenerated code:" + multiply_blend_8.codegen(codegen))
