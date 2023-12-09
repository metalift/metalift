from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int, Matrix
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tests.llvm.gaudi.gaudi_common import call_exp, call_map_int_to_int, call_matrix_vec_mul, call_reduce_sum, call_vec_elemwise_div, call_vec_elemwise_mul, call_vec_map, call_vec_scalar_mul, get_map_int_to_int_synth, matrix_vec_mul, reduce_sum, vec_elemwise_mul, an_arr2_to_arr, an_arr_to_int, a_matrix_and_vec_to_vec, reduce_mul, reduce_max, vec_elemwise_add, vec_elemwise_sub, vec_elemwise_div, map_int_to_int_fn_obj, vec_map, map_int_to_int, exp, vec_scalar_mul


def multiquery_attention_part1_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        matrix_vec_mul,
        reduce_sum,
        reduce_mul,
        reduce_max,
        vec_elemwise_add,
        vec_elemwise_sub,
        vec_elemwise_mul,
        vec_elemwise_div,
        vec_scalar_mul,
        vec_map,
        map_int_to_int,
        exp
    ]

def multiquery_attention_part1_ps_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    ret_val = writes[0]
    token_position, head, head_size, key_cache_layer, q = reads
    slice_start = head * head_size
    slice_end = slice_start + head_size
    key_cache_layer_slice = key_cache_layer[:token_position].col_slice(slice_start, slice_end)
    q_slice = q[slice_start:slice_end]
    lhs = call_matrix_vec_mul(key_cache_layer_slice, q_slice)
    rhs = call_vec_map(
        call_vec_scalar_mul(Int(1), lhs),
        map_int_to_int_fn_obj
    )
    return ret_val == call_vec_elemwise_div(lhs, rhs)

def multiquery_attention_part1_inv0_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    token_position, head, head_size, key_cache_layer, q = reads
    attention, i, score, timestep = writes
    slice_start = head * head_size
    slice_end = slice_start + head_size
    key_cache_layer_slice = key_cache_layer[:timestep].col_slice(slice_start, slice_end)
    q_slice = q[slice_start:slice_end]
    lhs = call_matrix_vec_mul(key_cache_layer_slice, q_slice)
    rhs = call_vec_map(
        call_vec_scalar_mul(Int(1), lhs),
        map_int_to_int_fn_obj
    )
    return and_objects(
        timestep >= 0,
        timestep <= token_position,
        attention == call_vec_elemwise_div(lhs, rhs)
    )

def multiquery_attention_part1_inv1_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    token_position, head, head_size, key_cache_layer, q = reads
    i, score = writes
    attention, timestep = in_scope
    slice_start = head * head_size
    curr_slice_end = slice_start + i
    slice_end = slice_start + head_size
    expected_score = call_reduce_sum(
        call_vec_elemwise_mul(
            q[slice_start:curr_slice_end],
            key_cache_layer[timestep][slice_start:curr_slice_end]
        )
    )
    attention_lhs = call_matrix_vec_mul(
        key_cache_layer[:timestep].col_slice(slice_start, slice_end),
        q[slice_start:slice_end]
    )
    attention_rhs = call_vec_map(
        call_vec_scalar_mul(Int(1), attention_lhs),
        map_int_to_int_fn_obj
    )
    return and_objects(
        timestep >= 0,
        timestep < token_position,
        i >= 0,
        i <= head_size,
        score == expected_score,
        attention == call_vec_elemwise_div(attention_lhs, attention_rhs)

    )


if __name__ == "__main__":
    driver = Driver()
    multiquery_attention_part1 = driver.analyze(
        llvm_filepath="tests/llvm/gaudi/multiquery_attention_part1.ll",
        loops_filepath="tests/llvm/gaudi/multiquery_attention_part1.loops",
        fn_name="multiquery_attention_part1",
        target_lang_fn=multiquery_attention_part1_target_lang,
        inv_grammars={
            "multiquery_attention_part1_inv0": InvGrammar(multiquery_attention_part1_inv0_grammar, []),
            "multiquery_attention_part1_inv1": InvGrammar(multiquery_attention_part1_inv1_grammar, ["timestep", "agg.result"])
        },
        ps_grammar=multiquery_attention_part1_ps_grammar
    )

    token_position_var = Int("token_position")
    head_var = Int("head")
    head_size_var = Int("head_size")
    key_cache_layer_var = Matrix(Int, "key_cache_layer")
    q_var = mlList(Int, "q")
    driver.add_var_objects([token_position_var, head_var, head_size_var, key_cache_layer_var, q_var])
    driver.add_precondition(token_position_var > 0)
    driver.add_precondition(key_cache_layer_var.len() > token_position_var)
    driver.add_precondition(head_var >= 0)
    driver.add_precondition(head_var <= q_var.len())
    driver.add_precondition(head_var <= key_cache_layer_var.len())
    driver.add_precondition(head_size_var > 0)
    driver.add_precondition(head_size_var <= q_var.len())
    driver.add_precondition(head_size_var <= key_cache_layer_var.len())
    driver.add_precondition((head_var * head_size_var + head_size_var) < key_cache_layer_var[0].len())
    driver.add_precondition((head_var * head_size_var + head_size_var) < q_var.len())

    multiquery_attention_part1(
        token_position_var,
        head_var,
        head_size_var,
        key_cache_layer_var,
        q_var,
        uninterp_fns=[exp.name()]
    )
    map_int_to_int_synth = get_map_int_to_int_synth()
    driver.fns_synths = [map_int_to_int_synth]
    driver.synthesize(noVerify=True)
