import time

from metalift.frontend.llvm import Driver
from metalift.ir import Int, Matrix
from tests.llvm.gaudi.gaudi_common import (
    get_nested_list_computation_inv0_grammar,
    get_nested_list_computation_inv1_grammar,
    get_nested_list_computation_ps_grammar_fn,
    nested_list_computation_target_lang, nested_list_mul8x8_div255_body,
    vec_mul8x8_div255_body)
from tests.python.utils.utils import codegen

if __name__ == "__main__":
    driver = Driver()
    inv0_grammar = get_nested_list_computation_inv0_grammar(
        fixed_grammar=True,
        fixed_out_fn=nested_list_mul8x8_div255_body
    )
    inv1_grammar = get_nested_list_computation_inv1_grammar(
        fixed_grammar=True,
        fixed_row_vec_fn=vec_mul8x8_div255_body,
        fixed_out_fn=nested_list_mul8x8_div255_body
    )
    ps_grammar = get_nested_list_computation_ps_grammar_fn(
        fixed_grammar=False,
        constants=[Int(255)],
        compute_ops=["*", "//"],
        depth=2
    )
    multiply_blend_8 = driver.analyze(
        llvm_filepath="tests/llvm/gaudi/multiply_blend_8.ll",
        loops_filepath="tests/llvm/gaudi/multiply_blend_8.loops",
        fn_name="multiply_blend_8",
        target_lang_fn=nested_list_computation_target_lang,
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
