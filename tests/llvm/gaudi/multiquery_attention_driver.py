from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int, Matrix
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tests.llvm.gaudi.gaudi_common import call_matrix_vec_mul, call_reduce_sum, call_vec_elemwise_mul, matrix_vec_mul, reduce_sum, vec_elemwise_mul, an_arr2_to_arr, an_arr_to_int, a_matrix_and_vec_to_vec, reduce_mul, reduce_max, vec_elemwise_add, vec_elemwise_sub, vec_elemwise_div


def multiquery_attention_part1_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        matrix_vec_mul,
        reduce_sum,
        reduce_mul,
        reduce_max,
        vec_elemwise_add,
        vec_elemwise_sub,
        vec_elemwise_mul,
        vec_elemwise_div
    ]

def multiquery_attention_part1_ps_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    ret_val = writes[0]
    token_position, head, head_size, key_cache_layer, q = reads
    slice_start = head * head_size
    slice_end = slice_start + head
    key_cache_layer_slice = key_cache_layer[:token_position][slice_start:slice_end]
    q_slice = q[slice_start:slice_end]
    return ret_val == call_matrix_vec_mul(key_cache_layer_slice, q_slice)

def multiquery_attention_part1_inv0_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    token_position, head, head_size, key_cache_layer, q = reads
    attention, i, score, timestep = writes
    slice_start = head * head_size
    slice_end = slice_start + head
    key_cache_layer_slice = key_cache_layer[:timestep][slice_start:slice_end]
    q_slice = q[slice_start:slice_end]
    return and_objects(
        timestep >= 0,
        timestep <= token_position,
        attention == call_matrix_vec_mul(key_cache_layer_slice, q_slice)
    )

def multiquery_attention_part1_inv1_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    token_position, head, head_size, key_cache_layer, q = reads
    i, score = writes
    attention, timestep = in_scope
    slice_start = head * head_size
    curr_slice_end = slice_start + i
    slice_end = slice_start + head
    return and_objects(
        timestep >= 0,
        timestep < token_position,
        i >= 0,
        i <= head_size,
        score == call_reduce_sum(
            call_vec_elemwise_mul(
                q[slice_start:curr_slice_end],
                key_cache_layer[timestep][slice_start:curr_slice_end]
            )
        ),
        attention == call_matrix_vec_mul(
            key_cache_layer[:timestep][slice_start:slice_end],
            q[slice_start:slice_end]
        )
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
    driver.add_precondition(token_position_var >= 0)
    driver.add_precondition(key_cache_layer_var.len() > token_position_var)
    driver.add_precondition(head_var >= 0)
    driver.add_precondition(head_size_var > 0)
    driver.add_precondition((head_var + 1) * head_size_var < key_cache_layer_var[0].len())
    driver.add_precondition((head_var + 1) * head_size_var < q_var.len())

    multiquery_attention_part1(
        token_position_var,
        head_var,
        head_size_var,
        key_cache_layer_var,
        q_var
    )
    driver.synthesize(noVerify=True)
