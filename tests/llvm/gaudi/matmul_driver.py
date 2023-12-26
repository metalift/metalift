from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int, Matrix
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tests.llvm.gaudi.gaudi_common import call_matrix_vec_mul, call_reduce_sum, call_vec_elemwise_mul, matrix_vec_mul, reduce_sum, vec_elemwise_mul, vec_vec_to_vec, vec_to_int, matrix_vec_to_vec, reduce_mul, reduce_max, vec_elemwise_add, vec_elemwise_sub, vec_elemwise_div, vec_to_int_target_lang, matrix_vec_to_vec_target_lang, vec_vec_to_vec_target_lang


def matmul_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return set(vec_to_int_target_lang + matrix_vec_to_vec_target_lang + vec_vec_to_vec_target_lang)

def matmul_ps_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    ret_val = writes[0]
    weight, input = reads
    return ret_val == matrix_vec_to_vec(weight, input)

def matmul_inv0_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    weight, input = reads
    out, col, _, row = writes
    row_lower_bound = choose(Int(0), Int(1))
    row_upper_bound = choose(weight.len(), input.len())
    matrix = choose(weight, weight[:row], weight[:col])
    vec = choose(input, input[:row], input[:col])

    return and_objects(
        row >= row_lower_bound,
        row <= row_upper_bound,
        out == matrix_vec_to_vec(matrix, vec)
    )

def matmul_inv1_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
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
        curr == vec_to_int(vec_vec_to_vec(vec, vec)),
        out == matrix_vec_to_vec(matrix, vec)
    )


if __name__ == "__main__":
    driver = Driver()
    matmul = driver.analyze(
        llvm_filepath="tests/llvm/gaudi/matmul.ll",
        loops_filepath="tests/llvm/gaudi/matmul.loops",
        fn_name="matmul",
        target_lang_fn=matmul_target_lang,
        inv_grammars={
            "matmul_inv0": InvGrammar(matmul_inv0_grammar, []),
            "matmul_inv1": InvGrammar(matmul_inv1_grammar, ["row", "agg.result"])
        },
        ps_grammar=matmul_ps_grammar
    )

    weight_var = Matrix(Int, "weight")
    input_var = mlList(Int, "input")
    driver.add_var_objects([weight_var, input_var])
    driver.add_precondition(weight_var.len() > 0)
    driver.add_precondition(weight_var[0].len() > 0)
    driver.add_precondition(weight_var[0].len() == input_var.len())

    matmul(weight_var, input_var)
    driver.synthesize()
