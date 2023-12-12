from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int, Matrix
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tests.llvm.gaudi.gaudi_common import matrix_vec_mul, reduce_sum, vec_elemwise_mul, vec_vec_to_vec, an_arr_to_int, a_matrix_and_vec_to_vec, reduce_mul, reduce_max, vec_elemwise_add, vec_elemwise_sub, vec_elemwise_div, vec_scalar_add, vec_scalar_div


def silu_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        matrix_vec_mul,
        reduce_sum,
        reduce_mul,
        reduce_max,
        vec_elemwise_add,
        vec_elemwise_sub,
        vec_elemwise_mul,
        vec_elemwise_div,
        vec_scalar_add,
        vec_scalar_div
    ]

def silu_ps_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    ret_val = writes[0]
    weight, input = reads
    return ret_val == a_matrix_and_vec_to_vec(weight, input)

def silu_inv0_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    weight, input = reads
    out, col, _, row = writes
    row_lower_bound = choose(Int(0), Int(1))
    row_upper_bound = choose(weight.len(), input.len())
    matrix = choose(weight, weight[:row], weight[:col])
    vec = choose(input, input[:row], input[:col])

    return and_objects(
        row >= row_lower_bound,
        row <= row_upper_bound,
        out == a_matrix_and_vec_to_vec(matrix, vec)
    )

def silu_inv1_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    col, curr = writes
    weight, input = reads
    out, row = in_scope
    lower_bound = choose(Int(0), Int(1))
    upper_bound = choose(weight.len(), input.len())
    matrix = choose(
        weight,
        weight[:row],
        weight[:col]
    )
    vec = choose(
        weight[row][:col],
        input[:col],
        input[:row],
        input
    )

    return and_objects(
        row >= lower_bound,
        row < upper_bound,
        col >= lower_bound,
        col <= upper_bound,
        curr == an_arr_to_int(vec_vec_to_vec(vec, vec)),
        out == a_matrix_and_vec_to_vec(matrix, vec)
    )


if __name__ == "__main__":
    driver = Driver()
    silu = driver.analyze(
        llvm_filepath="tests/llvm/gaudi/silu.ll",
        loops_filepath="tests/llvm/gaudi/silu.loops",
        fn_name="silu",
        target_lang_fn=silu_target_lang,
        inv_grammars={
            "silu_inv0": InvGrammar(silu_inv0_grammar, []),
            "silu_inv1": InvGrammar(silu_inv1_grammar, ["row", "agg.result"])
        },
        ps_grammar=silu_ps_grammar
    )

    input_var = mlList(Int, "input")
    hidden_dim_var = Int("hidden_dim")

    driver.add_var_objects([input_var, hidden_dim_var])
    driver.add_precondition(hidden_dim_var >= 0)
    driver.add_precondition(input_var.len() >= hidden_dim_var)

    silu(input_var, hidden_dim_var)
    driver.synthesize()
