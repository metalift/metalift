from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tests.llvm.gaudi.gaudi_common import (call_exp, call_scalar_vec_div,
                                           call_vec_elemwise_mul, call_vec_map,
                                           call_vec_scalar_add,
                                           get_map_int_to_int_synth,
                                           map_int_to_int_fn_obj,
                                           scalar_vec_to_vec_target_lang, sqrt,
                                           vec_to_vec_target_lang,
                                           vec_vec_to_vec_target_lang)


def elemwise_mul_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return vec_vec_to_vec_target_lang

def elemwise_mul_ps_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    ret_val = writes[0]
    input1, input2, hidden_dim = reads
    vec = choose(
        input1,
        input1[:hidden_dim],
        input2,
        input2[:hidden_dim]
    )
    return ret_val == call_vec_elemwise_mul(vec, vec)

def elemwise_mul_inv0_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    input1, input2, hidden_dim = reads
    out, i, _ = writes
    lower_bound = choose(Int(0), Int(1))
    upper_bound = choose(input1.len(), input2.len(), hidden_dim)
    vec = choose(
        input1,
        input1[:i],
        input1[:hidden_dim],
        input2,
        input2[:i],
        input2[:hidden_dim]
    )

    return and_objects(
        i >= lower_bound,
        i <= upper_bound,
        out == call_vec_elemwise_mul(vec, vec)
    )


if __name__ == "__main__":
    driver = Driver()
    elemwise_mul = driver.analyze(
        llvm_filepath="tests/llvm/gaudi/elemwise_mul.ll",
        loops_filepath="tests/llvm/gaudi/elemwise_mul.loops",
        fn_name="elemwise_mul",
        target_lang_fn=elemwise_mul_target_lang,
        inv_grammars={"elemwise_mul_inv0": InvGrammar(elemwise_mul_inv0_grammar, [])},
        ps_grammar=elemwise_mul_ps_grammar
    )

    input1_var = mlList(Int, "input1")
    input2_var = mlList(Int, "input2")
    hidden_dim_var = Int("hidden_dim")

    driver.add_var_objects([input1_var, input2_var, hidden_dim_var])
    driver.add_precondition(hidden_dim_var >= 0)
    driver.add_precondition(input1_var.len() >= hidden_dim_var)
    driver.add_precondition(input2_var.len() >= hidden_dim_var)

    elemwise_mul(input1_var, input2_var, hidden_dim_var)
    driver.synthesize(noVerify=True)
