from typing import List, Union
from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import BoolObject, FnDecl, FnDeclRecursive, IntObject, ListObject, NewObject, choose
from metalift.vc_util import and_objects
from tests.python.utils.utils import codegen
from tests.llvm.gaudi.gaudi_common import get_select_synth, nested_selection, call_nested_selection, select_fn_obj, call_selection, select_fn_decl, select_darken_blend_body,select_multiply_blend_body,select_linear_burn_body,select_color_burn_body,select_lighten_blend_body,select_screen_blend_body,select_linear_dodge_body,select_color_dodge_body,select_overlay_blend_body, selection_fn_decl, get_selection_synth
import time

def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [select_fn_decl, selection_fn_decl, nested_selection]

# def ps_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> BoolObject:
#     ret_val = writes[0]
#     base, active = reads
#     return ret_val == call_nested_selection(base, active, select_fn_obj)

# def inv0_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> BoolObject:
#     # outer loop grammar
#     out, col, row, row_vec = writes
#     base, active = reads
#     return and_objects(
#         row >= 0,
#         row <= base.len(),
#         out == call_nested_selection(base[:row], active[:row], select_fn_obj)
#     )

def inv1_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> BoolObject:
    # inner loop grammar
    col, row_vec = writes
    row = in_scope[0]
    base, active = reads
    return and_objects(
        row >= 0,
        row < base.len(),
        col >= 0,
        col <= base[0].len(),
        row_vec == call_selection(base[row][:col], active[row][:col], select_fn_obj),
    )

def ps_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> BoolObject:
    ret_val = writes[0]
    base, active = reads
    nested_list = choose(base, active)
    return ret_val == call_nested_selection(nested_list, nested_list, select_fn_obj)

def inv0_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> BoolObject:
    # outer loop grammar
    out, col, row, row_vec = writes
    base, active = reads
    index_lower_bound = choose(1 - IntObject(0), IntObject(0), IntObject(1))
    index_upper_bound = choose(base.len(), base[0].len(), row_vec.len())
    index = choose(row, col)
    index_lower_cond = choose(
        index >= index_lower_bound,
        index > index_lower_bound,
        index == index_lower_bound,
        index < index_lower_bound,
        index <= index_lower_bound
    )
    index_upper_cond = choose(
        index >= index_upper_bound,
        index > index_upper_bound,
        index == index_upper_bound,
        index < index_upper_bound,
        index <= index_upper_bound
    )
    nested_list = choose(
        base,
        base[:row],
        base[:col],
        active,
        active[:row],
        active[:col],
        out
    )
    return and_objects(
        index_lower_cond,
        index_upper_cond,
        nested_list == call_nested_selection(nested_list, nested_list, select_fn_obj)
    )

# def inv1_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> BoolObject:
#     # inner loop grammar
#     col, row_vec = writes
#     row = in_scope[0]
#     base, active = reads
#     index_lower_bound = choose(1 - IntObject(0), IntObject(0), IntObject(1))
#     index_upper_bound = choose(base.len(), base[0].len(), row_vec.len())
#     outer_index_lower_cond = choose(
#         row >= index_lower_bound,
#         row > index_lower_bound,
#         row == index_lower_bound,
#         row < index_lower_bound,
#         row <= index_lower_bound
#     )
#     outer_index_upper_cond = choose(
#         row >= index_upper_bound,
#         row > index_upper_bound,
#         row == index_upper_bound,
#         row < index_upper_bound,
#         row <= index_upper_bound
#     )
#     inner_index_lower_cond = choose(
#         col >= index_lower_bound,
#         col > index_lower_bound,
#         col == index_lower_bound,
#         col < index_lower_bound,
#         col <= index_lower_bound
#     )
#     inner_index_upper_cond = choose(
#         col >= index_upper_bound,
#         col > index_upper_bound,
#         col == index_upper_bound,
#         col < index_upper_bound,
#         col <= index_upper_bound
#     )
#     vec = choose(
#         base[0][:col],
#         base[row][:col],
#         base[col][:row],
#         base[0][:row],
#         active[0][:col],
#         active[row][:col],
#         active[col][:row],
#         active[0][:row],
#         row_vec
#     )
#     return and_objects(
#         outer_index_lower_cond,
#         outer_index_upper_cond,
#         inner_index_lower_cond,
#         inner_index_upper_cond,
#         vec == call_selection(vec, vec, select_fn_obj),
#     )

if __name__ == "__main__":
    driver = Driver()
    darken_blend_8 = driver.analyze(
        llvm_filepath="tests/llvm/gaudi/darken_blend_8.ll",
        loops_filepath="tests/llvm/gaudi/darken_blend_8.loops",
        fn_name="darken_blend_8",
        target_lang_fn=target_lang,
        inv_grammars={
            "darken_blend_8_inv0": InvGrammar(inv0_grammar, []),
            "darken_blend_8_inv1": InvGrammar(inv1_grammar, ["row", "row_vec"])
        },
        ps_grammar=ps_grammar
    )

    base = ListObject(ListObject[IntObject], "base")
    active = ListObject(ListObject[IntObject], "active")
    int_x, int_y = IntObject("int_x"), IntObject("int_y")
    x, y = ListObject(IntObject, "x"), ListObject(IntObject, "y")
    driver.add_var_objects([base, active, int_x, int_y, x, y])

    # Add preconditions
    driver.add_precondition(base.len() > 1)
    driver.add_precondition(base.len() == active.len())
    driver.add_precondition(base[0].len() == active[0].len())

    possible_bodies = [
        select_multiply_blend_body(int_x, int_y),
        select_linear_burn_body(int_x, int_y),
        select_color_burn_body(int_x, int_y),
        select_lighten_blend_body(int_x, int_y),
        select_screen_blend_body(int_x, int_y),
        select_linear_dodge_body(int_x, int_y),
        select_color_dodge_body(int_x, int_y),
        select_overlay_blend_body(int_x, int_y),
        select_darken_blend_body(int_x, int_y)
    ]

    driver.fns_synths = [
        get_select_synth(possible_bodies, [int_x, int_y]),
        get_selection_synth(x, y, select_fn_obj)
    ]
    darken_blend_8(base, active)

    start_time = time.time()
    driver.synthesize(noVerify=True)
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
    print("\n\ngenerated code:" + darken_blend_8.codegen(codegen))


