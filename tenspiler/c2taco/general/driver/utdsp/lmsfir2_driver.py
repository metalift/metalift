import argparse
import time
from collections import defaultdict
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
    vec_slice_fn_decl,
    vec_to_int_target_lang,
    vec_to_vec_target_lang,
    vec_vec_to_vec_target_lang,
)


def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        *vec_vec_to_vec_target_lang,
        *scalar_vec_to_vec_target_lang,
        *vec_to_int_target_lang,
        *vec_to_vec_target_lang,
        vec_slice_fn_decl,
    ]


def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    ntaps, input, coefficient, error = reads
    out = writes[0]
    vec = choose(input, coefficient)
    int_var = choose(Int(0), ntaps - 1, error).maybe_relaxed(parser_args.relaxed)
    slice_index = get_int_expr_eq_or_below_depth(int_var, depth=parser_args.depth)
    vec = choose(vec[slice_index:slice_index])
    vec = get_matrix_or_vec_expr_eq_or_below_depth(
        matrix_or_vec_var=vec, int_var=int_var, depth=parser_args.depth
    )
    return out == vec


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    ntaps, input, coefficient, error = reads
    out, _, i = writes
    vec = choose(input, coefficient)
    int_var = choose(Int(0), ntaps - 1, i, error).maybe_relaxed(parser_args.relaxed)
    slice_index = get_int_expr_eq_or_below_depth(int_var, parser_args.depth)
    vec = choose(vec[slice_index:slice_index])
    vec = get_matrix_or_vec_expr_eq_or_below_depth(
        matrix_or_vec_var=vec, int_var=int_var, depth=parser_args.depth
    )
    lower_bound, upper_bound = Int(0), ntaps - 1
    return and_objects(
        i >= lower_bound.maybe_relaxed(parser_args.relaxed),
        i <= upper_bound.maybe_relaxed(parser_args.relaxed),
        out == vec,
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, required=True)
    parser.add_argument("--relaxed", action="store_true", default=False)
    parser_args = parser.parse_args()

    driver = Driver()
    lmsfir2 = driver.analyze(
        "tenspiler/c2taco/cpp/for_synthesis/utdsp/lmsfir2.ll",
        "tenspiler/c2taco/cpp/for_synthesis/utdsp/lmsfir2.loops",
        "lmsfir2",
        target_lang,
        defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar,
    )

    ntaps = Int("NTAPS")
    input = mlList(Int, "input")
    coefficient = mlList(Int, "coefficient")
    error = Int("error")

    driver.add_var_objects([ntaps, input, coefficient, error])
    driver.add_precondition(ntaps >= 1)
    driver.add_precondition(input.len() >= ntaps)
    driver.add_precondition(coefficient.len() >= ntaps)

    map_int_to_int_synth = get_map_int_to_int_synth()
    driver.fns_synths = [
        map_int_to_int_synth,
    ]

    lmsfir2(ntaps, input, coefficient, error)

    start_time = time.time()
    relaxed_suffix = "_relaxed" if parser_args.relaxed else ""
    depth_suffix = f"_depth{parser_args.depth}"
    driver.synthesize(filename=f"lmsfir2{depth_suffix}{relaxed_suffix}", no_verify=True)
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
