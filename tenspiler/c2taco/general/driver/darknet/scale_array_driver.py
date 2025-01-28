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
    vec_to_int_target_lang,
    vec_to_vec_target_lang,
    vec_vec_to_vec_target_lang,
)


def scale_array_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        *vec_vec_to_vec_target_lang,
        *scalar_vec_to_vec_target_lang,
        *vec_to_vec_target_lang,
        *vec_to_int_target_lang,
    ]


def scale_array_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    a, n, s = reads
    out = writes[0]
    int_var = choose(Int(0), n, s).maybe_relaxed(parser_args.relaxed)
    slice_index = get_int_expr_eq_or_below_depth(int_var, depth=parser_args.depth)
    vec = a[slice_index:slice_index]
    vec = get_matrix_or_vec_expr_eq_or_below_depth(
        vec, int_var=int_var, depth=parser_args.depth
    )
    return out == vec


def scale_array_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    a, n, s = reads
    out, i, _ = writes
    lower_bound = Int(0)
    upper_bound = n
    int_var = choose(lower_bound, upper_bound, i, s).maybe_relaxed(parser_args.relaxed)
    slice_index = get_int_expr_eq_or_below_depth(int_var, parser_args.depth)
    vec = a[slice_index:slice_index]
    vec = get_matrix_or_vec_expr_eq_or_below_depth(
        vec, int_var=int_var, depth=parser_args.depth
    )

    return and_objects(
        i >= lower_bound.maybe_relaxed(parser_args.relaxed),
        i <= upper_bound.maybe_relaxed(parser_args.relaxed),
        out == vec,
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, required=True)
    parser.add_argument("--relaxed", action="store_true")
    parser_args = parser.parse_args()

    driver = Driver()
    scale_array = driver.analyze(
        "tenspiler/c2taco/cpp/for_synthesis/darknet/scale_array.ll",
        "tenspiler/c2taco/cpp/for_synthesis/darknet/scale_array.loops",
        "scale_array",
        scale_array_target_lang,
        defaultdict(lambda: InvGrammar(scale_array_inv0_grammar, [])),
        scale_array_ps_grammar,
    )

    a = mlList(Int, "a")
    n = Int("n")
    s = Int("s")

    driver.add_var_objects([a, n, s])
    driver.add_precondition(n >= 1)
    driver.add_precondition(a.len() >= n)

    map_int_to_int_synth = get_map_int_to_int_synth()
    driver.fns_synths = [
        map_int_to_int_synth,
    ]

    scale_array(a, n, s)

    start_time = time.time()
    relaxed_suffix = "_relaxed" if parser_args.relaxed else ""
    depth_suffix = f"_depth{parser_args.depth}"
    driver.synthesize(filename=f"scale_array{depth_suffix}{relaxed_suffix}")
    end_time = time.time()

    print(f"Synthesis took {end_time - start_time} seconds")
