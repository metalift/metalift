import time
from typing import List

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tests.llvm.gaudi.gaudi_common import (call_nested_selection_two_args,
                                           call_selection_two_args,
                                           nested_list_computation,
                                           nested_list_computation_target_lang,
                                           select_two_args_fn_obj,
                                           select_two_args_general_synth,
                                           selection_two_args_synth,
                                           selection_two_args_target_lang,
                                           vec_computation)
from tests.python.utils.utils import codegen


def ps_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    ret_val = writes[0]
    base, active = reads
    base_or_active = choose(base, active)
    select_or_compute = choose(
        call_nested_selection_two_args(base_or_active, base_or_active, select_two_args_fn_obj),
        nested_list_computation(base_or_active, base_or_active),
    )
    return ret_val == select_or_compute

def inv0_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    # outer loop grammar
    out, col, pixel, row, row_vec = writes
    base, active = reads
    index_lower_bound = choose(Int(0), Int(1))
    index_upper_bound = choose(base.len(), base[0].len())
    index_lower_cond = choose(
        row >= index_lower_bound,
        row > index_lower_bound,
        row == index_lower_bound,
        row < index_lower_bound,
        row <= index_lower_bound
    )
    index_upper_cond = choose(
        row >= index_upper_bound,
        row > index_upper_bound,
        row == index_upper_bound,
        row < index_upper_bound,
        row <= index_upper_bound
    )
    nested_list = choose(
        base,
        base[:row],
        base[:col],
        active,
        active[:row],
        active[:col],
    )
    select_or_compute = choose(
        call_nested_selection_two_args(nested_list, nested_list, select_two_args_fn_obj),
        nested_list_computation(nested_list, nested_list)
    )
    return and_objects(
        index_lower_cond,
        index_upper_cond,
        out == select_or_compute
    )

def inv1_grammar_fn(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    # inner loop grammar
    col, pixel, row_vec = writes
    out, row = in_scope
    base, active = reads
    index_lower_bound = choose(Int(0), Int(1))
    index_upper_bound = choose(base.len(), base[0].len())
    outer_index_lower_cond = choose(
        row >= index_lower_bound,
        row > index_lower_bound,
        row == index_lower_bound,
        row < index_lower_bound,
        row <= index_lower_bound
    )
    outer_index_upper_cond = choose(
        row >= index_upper_bound,
        row > index_upper_bound,
        row == index_upper_bound,
        row < index_upper_bound,
        row <= index_upper_bound
    )
    inner_index_lower_cond = choose(
        col >= index_lower_bound,
        col > index_lower_bound,
        col == index_lower_bound,
        col < index_lower_bound,
        col <= index_lower_bound
    )
    inner_index_upper_cond = choose(
        col >= index_upper_bound,
        col > index_upper_bound,
        col == index_upper_bound,
        col < index_upper_bound,
        col <= index_upper_bound
    )
    vec = choose(
        base[0][:col],
        base[row][:col],
        base[col][:row],
        base[0][:row],
        active[0][:col],
        active[row][:col],
        active[col][:row],
        active[0][:row],
        row_vec
    )
    nested_list = choose(
        base,
        base[:row],
        base[:col],
        active,
        active[:row],
        active[:col]
    )
    row_vec_select_or_compute = choose(
        call_selection_two_args(vec, vec, select_two_args_fn_obj),
        vec_computation(vec, vec)
    )
    out_select_or_compute = choose(
        call_nested_selection_two_args(nested_list, nested_list, select_two_args_fn_obj),
        nested_list_computation(nested_list, nested_list)
    )
    return and_objects(
        outer_index_lower_cond,
        outer_index_upper_cond,
        inner_index_lower_cond,
        inner_index_upper_cond,
        row_vec == row_vec_select_or_compute,
        out == out_select_or_compute
    )


if __name__ == "__main__":
    driver = Driver()
    darken_blend_8 = driver.analyze(
        llvm_filepath="tests/llvm/gaudi/darken_blend_8.ll",
        loops_filepath="tests/llvm/gaudi/darken_blend_8.loops",
        fn_name="darken_blend_8",
        target_lang_fn=lambda: selection_two_args_target_lang() + nested_list_computation_target_lang(),
        inv_grammars={
            "darken_blend_8_inv0": InvGrammar(inv0_grammar_fn, []),
            "darken_blend_8_inv1": InvGrammar(inv1_grammar_fn, ["row", "agg.result"])
        },
        ps_grammar=ps_grammar_fn
    )

    base = mlList(mlList[Int], "base")
    active = mlList(mlList[Int], "active")
    driver.add_var_objects([base, active])

    # Add preconditions
    driver.add_precondition(base.len() > 1)
    driver.add_precondition(base.len() == active.len())
    driver.add_precondition(base[0].len() == active[0].len())

    driver.fns_synths = [select_two_args_general_synth, selection_two_args_synth]
    darken_blend_8(base, active)

    start_time = time.time()
    driver.synthesize(listBound=3, noVerify=True)
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
    print("\n\ngenerated code:" + darken_blend_8.codegen(codegen))


