from collections import OrderedDict
import time

from metalift.frontend.llvm import Driver
from metalift.ir import Int, Matrix
from tests.llvm.hardlift.hardlift_common import (
    get_matrix_computation_hole_inv0_grammar,
    get_matrix_computation_hole_inv1_grammar,
    get_matrix_computation_hole_ps_grammar,
    get_multi_depth_compute_with_counts_general_synth,
    screen_blend_8_hole_body,
    matrix_computation_target_lang
)
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
    constants = [Int(32)]
    inv0_hole_grammar = get_matrix_computation_hole_inv0_grammar(constants, screen_blend_8_hole_body)
    inv1_hole_grammar = get_matrix_computation_hole_inv1_grammar(constants, screen_blend_8_hole_body)
    ps_hole_grammar = get_matrix_computation_hole_ps_grammar(constants, screen_blend_8_hole_body)
    screen_blend_8 = driver.analyze(
        llvm_filepath="tests/llvm/gaudi/screen_blend_8.ll",
        loops_filepath="tests/llvm/gaudi/screen_blend_8.loops",
        fn_name="screen_blend_8",
        target_lang_fn=matrix_computation_target_lang,
        inv_grammars={
            "screen_blend_8_inv0": inv0_hole_grammar,
            "screen_blend_8_inv1": inv1_hole_grammar
        },
        ps_grammar=ps_hole_grammar
    )

    base = Matrix(Int, "base")
    active = Matrix(Int, "active")
    driver.add_var_objects([base, active])

    # Add preconditions
    driver.add_precondition(base.len() > 1)
    driver.add_precondition(base.len() == active.len())
    driver.add_precondition(base[0].len() == active[0].len())

    screen_blend_8(base, active)

    start_time = time.time()
    driver.synthesize(listBound=2, noVerify=True)
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
    print("\n\ngenerated code:" + screen_blend_8.codegen(codegen))
