import time

from metalift.frontend.llvm import Driver
from metalift.ir import IntObject, ListObject
from tests.llvm.gaudi.gaudi_common import (all_possible_selects_two_args_synth,
                                           selection_two_args_inv0_grammar,
                                           selection_two_args_inv1_grammar,
                                           selection_two_args_ps_grammar_fn,
                                           selection_two_args_synth,
                                           selection_two_args_target_lang)
from tests.python.utils.utils import codegen

if __name__ == "__main__":
    driver = Driver()
    multiply_blend_8 = driver.analyze(
        llvm_filepath="tests/llvm/gaudi/multiply_blend_8.ll",
        loops_filepath="tests/llvm/gaudi/multiply_blend_8.loops",
        fn_name="multiply_blend_8",
        target_lang_fn=selection_two_args_target_lang,
        inv_grammars={
            "multiply_blend_8_inv0": selection_two_args_inv0_grammar,
            "multiply_blend_8_inv1": selection_two_args_inv1_grammar
        },
        ps_grammar=selection_two_args_ps_grammar_fn
    )

    base = ListObject(ListObject[IntObject], "base")
    active = ListObject(ListObject[IntObject], "active")
    driver.add_var_objects([base, active])

    # Add preconditions
    driver.add_precondition(base.len() > 1)
    driver.add_precondition(base.len() == active.len())
    driver.add_precondition(base[0].len() == active[0].len())

    driver.fns_synths = [all_possible_selects_two_args_synth, selection_two_args_synth]
    multiply_blend_8(base, active)

    start_time = time.time()
    driver.synthesize(listBound=3, noVerify=True)
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
    print("\n\ngenerated code:" + multiply_blend_8.codegen(codegen))
