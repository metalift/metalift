from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tenspiler.tenspiler_common import (
    call_integer_exp,
    call_scalar_vec_div,
    call_scalar_vec_sub,
    call_vec_elemwise_mul,
    call_vec_map,
    call_vec_scalar_add,
    get_map_int_to_int_synth,
    map_int_to_int,
    map_int_to_int_fn_obj,
    scalar_vec_div,
    scalar_vec_sub,
    vec_elemwise_mul,
    vec_map,
    vec_scalar_add,
)


def transformer_part3_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        scalar_vec_sub,
        scalar_vec_div,
        vec_scalar_add,
        vec_elemwise_mul,
        vec_map,
        map_int_to_int,
    ]


def transformer_part3_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    ret_val = writes[0]
    input, hidden_dim = reads
    vec = choose(input[:hidden_dim])
    negative_vec = call_scalar_vec_sub(Int(0), vec)
    cons = choose(Int(1))
    return ret_val == call_vec_elemwise_mul(
        vec,
        call_scalar_vec_div(
            cons,
            call_vec_scalar_add(
                cons, call_vec_map(negative_vec, map_int_to_int_fn_obj)
            ),
        ),
    )


def transformer_part3_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    input, hidden_dim = reads
    out, _, i = writes
    vec = choose(input[:i])
    negative_vec = call_scalar_vec_sub(Int(0), vec)
    cons = choose(Int(1))
    return and_objects(
        i >= 0,
        i <= hidden_dim,
        out
        == call_vec_elemwise_mul(
            vec,
            call_scalar_vec_div(
                cons,
                call_vec_scalar_add(
                    cons, call_vec_map(negative_vec, map_int_to_int_fn_obj)
                ),
            ),
        ),
    )


if __name__ == "__main__":
    driver = Driver()
    transformer_part3 = driver.analyze(
        llvm_filepath="tenspiler/llama/cpp/for_synthesis/transformer/transformer_part3.ll",
        loops_filepath="tenspiler/llama/cpp/for_synthesis/transformer/transformer_part3.loops",
        fn_name="transformer_part3",
        target_lang_fn=transformer_part3_target_lang,
        inv_grammars={
            "transformer_part3_inv0": InvGrammar(transformer_part3_inv0_grammar, [])
        },
        ps_grammar=transformer_part3_ps_grammar,
    )

    input_var = mlList(Int, "input")
    hidden_dim_var = Int("hidden_dim")

    driver.add_var_objects([input_var, hidden_dim_var])
    driver.add_precondition(hidden_dim_var >= 0)
    driver.add_precondition(input_var.len() >= hidden_dim_var)

    transformer_part3(input_var, hidden_dim_var)
    int_x = Int("int_x")
    map_int_to_int_synth = get_map_int_to_int_synth([call_integer_exp(int_x)])
    driver.fns_synths = [map_int_to_int_synth]
    driver.synthesize(filename="transformer_part3", no_verify=True)
