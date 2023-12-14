from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tests.llvm.gaudi.gaudi_common import (call_exp, call_scalar_vec_div, call_sqrt,
                                           call_vec_elemwise_mul, call_vec_map,
                                           call_vec_scalar_add,
                                           get_map_int_to_int_synth,
                                           map_int_to_int_fn_obj,
                                           scalar_vec_to_vec_target_lang, sqrt,
                                           vec_to_vec_target_lang,
                                           vec_vec_to_vec_target_lang)


def silu_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return scalar_vec_to_vec_target_lang + vec_vec_to_vec_target_lang + vec_to_vec_target_lang

def silu_ps_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    ret_val = writes[0]
    input, hidden_dim = reads
    vec = choose(input, input[:hidden_dim])
    return ret_val == call_vec_elemwise_mul(
        call_scalar_vec_div(
            Int(1),
            call_vec_scalar_add(Int(1), call_vec_map(vec, map_int_to_int_fn_obj))
        ),
        vec
    )

def silu_inv0_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    input, hidden_dim = reads
    out, _, i, _ = writes
    lower_bound = choose(Int(0), Int(1))
    upper_bound = choose(input.len(), hidden_dim)
    vec = choose(input, input[:i], input[:hidden_dim])

    return and_objects(
        i >= lower_bound,
        i <= upper_bound,
        out == call_vec_elemwise_mul(
            call_scalar_vec_div(
                Int(1),
                call_vec_scalar_add(Int(1), call_vec_map(vec, map_int_to_int_fn_obj))
            ),
            vec
        )
    )


if __name__ == "__main__":
    driver = Driver()
    silu = driver.analyze(
        llvm_filepath="tests/llvm/gaudi/silu.ll",
        loops_filepath="tests/llvm/gaudi/silu.loops",
        fn_name="silu",
        target_lang_fn=silu_target_lang,
        inv_grammars={"silu_inv0": InvGrammar(silu_inv0_grammar, [])},
        ps_grammar=silu_ps_grammar
    )

    input_var = mlList(Int, "input")
    hidden_dim_var = Int("hidden_dim")

    driver.add_var_objects([input_var, hidden_dim_var])
    driver.add_precondition(hidden_dim_var >= 0)
    driver.add_precondition(input_var.len() >= hidden_dim_var)

    silu(input_var, hidden_dim_var, uninterp_fns=[sqrt.name()])
    int_x = Int("int_x")
    map_int_to_int_synth = get_map_int_to_int_synth([call_sqrt(int_x)])
    driver.fns_synths = [map_int_to_int_synth]
    driver.synthesize()
