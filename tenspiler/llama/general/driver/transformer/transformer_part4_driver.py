import argparse
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tenspiler.tenspiler_common import (
    get_int_expr_eq_or_below_depth,
    get_map_int_to_int_synth,
    get_matrix_or_vec_expr_eq_or_below_depth,
    scalar_vec_to_vec_target_lang,
    vec_to_vec_target_lang,
    vec_vec_to_vec_target_lang,
)


def transformer_part4_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        *vec_vec_to_vec_target_lang,
        *scalar_vec_to_vec_target_lang,
        *vec_to_vec_target_lang,
    ]


def transformer_part4_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    ret_val = writes[0]
    input1, input2, hidden_dim = reads
    lower_bound = Int(0)
    upper_bound = hidden_dim
    slice_index = choose(lower_bound, upper_bound, Int(1)).maybe_relaxed(
        parser_args.relaxed
    )
    slice_index = get_int_expr_eq_or_below_depth(slice_index, depth=parser_args.depth)
    vec = choose(
        input1[slice_index:slice_index],
        input2[slice_index:slice_index],
    )
    return ret_val == get_matrix_or_vec_expr_eq_or_below_depth(
        matrix_or_vec_var=vec, int_vars=[Int(0), Int(1)], depth=parser_args.depth
    )


def transformer_part4_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    input1, input2, hidden_dim = reads
    out, i, _ = writes
    lower_bound = Int(0)
    upper_bound = hidden_dim
    slice_index = choose(lower_bound, upper_bound, i, Int(1)).maybe_relaxed(
        parser_args.relaxed
    )
    slice_index = get_int_expr_eq_or_below_depth(slice_index, depth=parser_args.depth)
    vec = choose(
        input1[slice_index:slice_index],
        input2[slice_index:slice_index],
    )

    return and_objects(
        i >= lower_bound.maybe_relaxed(parser_args.relaxed),
        i <= upper_bound.maybe_relaxed(parser_args.relaxed),
        out
        == get_matrix_or_vec_expr_eq_or_below_depth(
            matrix_or_vec_var=vec, int_vars=[Int(0), Int(1)], depth=parser_args.depth
        ),
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int)
    parser.add_argument("--relaxed", action="store_true")
    parser_args = parser.parse_args()

    driver = Driver()
    transformer_part4 = driver.analyze(
        llvm_filepath="tenspiler/llama/cpp/rmsnorm/transformer/transformer_part4.ll",
        loops_filepath="tenspiler/llama/cpp/rmsnorm/transformer/transformer_part4.loops",
        fn_name="transformer_part4",
        target_lang_fn=transformer_part4_target_lang,
        inv_grammars={
            "transformer_part4_inv0": InvGrammar(transformer_part4_inv0_grammar, [])
        },
        ps_grammar=transformer_part4_ps_grammar,
    )

    input1_var = mlList(Int, "input1")
    input2_var = mlList(Int, "input2")
    hidden_dim_var = Int("hidden_dim")

    driver.add_var_objects([input1_var, input2_var, hidden_dim_var])
    driver.add_precondition(hidden_dim_var >= 0)
    driver.add_precondition(input1_var.len() >= hidden_dim_var)
    driver.add_precondition(input2_var.len() >= hidden_dim_var)

    transformer_part4(input1_var, input2_var, hidden_dim_var)
    map_int_to_int_synth = get_map_int_to_int_synth()
    driver.fns_synths = [map_int_to_int_synth]

    relaxed_suffix = "_relaxed" if parser_args.relaxed else ""
    depth_suffix = f"_depth{parser_args.depth}"
    driver.synthesize(filename=f"transformer_part4{depth_suffix}{relaxed_suffix}")
