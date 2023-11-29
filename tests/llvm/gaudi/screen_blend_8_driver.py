from collections import OrderedDict
import time

from metalift.frontend.llvm import Driver
from metalift.ir import Int, Matrix, synth
from tests.llvm.gaudi.gaudi_common import (
    FIXED_SELECT_TWO_ARGS,
    get_multi_depth_compute_with_counts_general_synth,
    get_multi_depth_with_counts_select_general_synth,
    get_nested_list_computation_grammars_without_analysis,
    get_nested_list_computation_with_counts_inv0_grammar,
    get_nested_list_computation_with_counts_inv1_grammar,
    get_nested_list_computation_with_counts_ps_grammar_fn,
    nested_list_computation_target_lang,
    nested_list_screen8x8_body,
    selection_two_args_inv0_grammar,
    selection_two_args_inv1_grammar,
    screen8x8_body,
    selection_two_args_inv0_grammar_fn,
    selection_two_args_inv1_grammar_fn,
    selection_two_args_ps_grammar_fn,
    selection_two_args_target_lang,
    vec_screen8x8_body)
from tests.python.utils.utils import codegen

if __name__ == "__main__":
    driver = Driver()
    int_x, int_y = Int("int_x"), Int("int_y")
    ordered_compute_ops = OrderedDict()
    ordered_compute_ops["+"] = 1
    ordered_compute_ops["-"] = 1
    ordered_compute_ops["*"] = 1
    ordered_compute_ops["//"] = 1
    select_synth = get_multi_depth_compute_with_counts_general_synth(
        args=[int_x, int_y],
        constants=[Int(32)],
        ordered_compute_ops=ordered_compute_ops,
        depth=3
    )
    # fixed_select_synth = synth(
    #     FIXED_SELECT_TWO_ARGS,
    #     screen8x8_body(int_x, int_y),
    #     int_x,
    #     int_y
    # )
    # inv0_grammar = get_nested_list_computation_with_counts_inv0_grammar(
    #     fixed_grammar=True,
    #     fixed_out_fn=nested_list_screen8x8_body
    # )
    # inv1_grammar = get_nested_list_computation_with_counts_inv1_grammar(
    #     fixed_grammar=True,
    #     fixed_row_vec_fn=vec_screen8x8_body,
    #     fixed_out_fn=nested_list_screen8x8_body
    # )
    # ps_grammar = get_nested_list_computation_with_counts_ps_grammar_fn(
    #     fixed_grammar=False,
    #     constants=[Int(32)],
    #     ordered_compute_ops=ordered_compute_ops,
    #     depth=3
    # )

    screen_blend_8 = driver.analyze(
        llvm_filepath="tests/llvm/gaudi/screen_blend_8.ll",
        loops_filepath="tests/llvm/gaudi/screen_blend_8.loops",
        fn_name="screen_blend_8",
        target_lang_fn=selection_two_args_target_lang,
        inv_grammars={
            "screen_blend_8_inv0": selection_two_args_inv0_grammar,
            "screen_blend_8_inv1": selection_two_args_inv1_grammar
        },
        ps_grammar=selection_two_args_ps_grammar_fn
    )

    base = Matrix(Int, "base")
    active = Matrix(Int, "active")
    driver.add_var_objects([base, active])

    # Add preconditions
    driver.add_precondition(base.len() > 1)
    driver.add_precondition(base.len() == active.len())
    driver.add_precondition(base[0].len() == active[0].len())
    driver.fns_synths = [select_synth]


    screen_blend_8(base, active)

    start_time = time.time()
    driver.synthesize(listBound=3, noVerify=True)
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
    print("\n\ngenerated code:" + screen_blend_8.codegen(codegen))
