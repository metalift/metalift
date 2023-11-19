import time

from metalift.frontend.llvm import Driver
from metalift.ir import Int, Matrix
from tests.llvm.gaudi.gaudi_common import (
    call_nested_list_elemwise_add, call_vec_elemwise_add,
    get_nested_list_computation_inv0_grammar,
    get_nested_list_computation_inv1_grammar,
    get_nested_list_computation_ps_grammar_fn,
    nested_list_computation_target_lang)
from tests.python.utils.utils import codegen

if __name__ == "__main__":
    driver = Driver()
    inv0_grammar = get_nested_list_computation_inv0_grammar(
        fixed_grammar=True,
        fixed_out_fn=call_nested_list_elemwise_add
    )
    inv1_grammar = get_nested_list_computation_inv1_grammar(
        fixed_grammar=True,
        fixed_row_vec_fn=call_vec_elemwise_add,
        fixed_out_fn=call_nested_list_elemwise_add
    )
    ps_grammar = get_nested_list_computation_ps_grammar_fn(
        fixed_grammar=False,
        constants=[],
        compute_ops=["+"],
        depth=1
    )
    linear_dodge_8 = driver.analyze(
        llvm_filepath="tests/llvm/gaudi/linear_dodge_8.ll",
        loops_filepath="tests/llvm/gaudi/linear_dodge_8.loops",
        fn_name="linear_dodge_8",
        target_lang_fn=nested_list_computation_target_lang,
        inv_grammars={
            "linear_dodge_8_inv0": inv0_grammar,
            "linear_dodge_8_inv1": inv1_grammar
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

    linear_dodge_8(base, active)

    start_time = time.time()
    driver.synthesize(listBound=3, noVerify=True)
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
    print("\n\ngenerated code:" + linear_dodge_8.codegen(codegen))
