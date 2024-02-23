import argparse
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tenspiler.tenspiler_common import (
    call_integer_exp,
    get_map_int_to_int_synth,
    get_matrix_or_vec_expr_eq_or_below_depth,
    map_int_to_int,
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
    lower_bound = Int(0)
    upper_bound = hidden_dim
    slice_index = choose(lower_bound, upper_bound, Int(1)).maybe_relaxed(
        parser_args.relaxed
    )
    vec = input[slice_index:slice_index]
    return ret_val == get_matrix_or_vec_expr_eq_or_below_depth(
        matrix_or_vec_var=vec, int_vars=[Int(1), hidden_dim], depth=parser_args.depth
    )


def transformer_part3_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    input, hidden_dim = reads
    out, _, i = writes
    lower_bound = Int(0)
    upper_bound = hidden_dim
    slice_index = choose(lower_bound, upper_bound, i, Int(1)).maybe_relaxed(
        parser_args.relaxed
    )
    vec = input[slice_index:slice_index]
    return and_objects(
        i >= 0,
        i <= hidden_dim,
        out
        == get_matrix_or_vec_expr_eq_or_below_depth(
            matrix_or_vec_var=vec,
            int_vars=[Int(1), hidden_dim],
            depth=parser_args.depth,
        ),
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int)
    parser.add_argument("--relaxed", action="store_true")
    parser_args = parser.parse_args()

    driver = Driver()
    transformer_part3 = driver.analyze(
        llvm_filepath="tenspiler/llama/cpp/rmsnorm/transformer/transformer_part3.ll",
        loops_filepath="tenspiler/llama/cpp/rmsnorm/transformer/transformer_part3.loops",
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

    relaxed_suffix = "_relaxed" if parser_args.relaxed else ""
    depth_suffix = f"_depth{parser_args.depth}"
    driver.synthesize(filename=f"transformer_part3{depth_suffix}{relaxed_suffix}")
