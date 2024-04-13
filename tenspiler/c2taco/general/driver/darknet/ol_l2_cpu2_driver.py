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


def ol_l2_cpu2_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        *vec_vec_to_vec_target_lang,
        *scalar_vec_to_vec_target_lang,
        *vec_to_vec_target_lang,
        *vec_to_int_target_lang,
    ]


def ol_l2_cpu2_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    n, pred, truth = reads
    delta = writes[0]
    int_var = choose(Int(0), n).maybe_relaxed(parser_args.relaxed)
    slice_index = get_int_expr_eq_or_below_depth(int_var, depth=parser_args.depth)
    vec = choose(pred, truth)
    vec = vec[slice_index:slice_index]
    vec = get_matrix_or_vec_expr_eq_or_below_depth(
        vec, int_var=int_var, depth=parser_args.depth
    )
    return delta == vec


def ol_l2_cpu2_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    n, pred, truth = reads
    delta, _, i = writes
    lower_bound = Int(0)
    upper_bound = n
    int_var = choose(lower_bound, upper_bound, i).maybe_relaxed(parser_args.relaxed)
    slice_index = get_int_expr_eq_or_below_depth(int_var, parser_args.depth)
    vec = choose(pred, truth)
    vec = vec[slice_index:slice_index]
    vec = get_matrix_or_vec_expr_eq_or_below_depth(
        vec, int_var=int_var, depth=parser_args.depth
    )

    return and_objects(
        i >= lower_bound.maybe_relaxed(parser_args.relaxed),
        i <= upper_bound.maybe_relaxed(parser_args.relaxed),
        delta == vec,
    )


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--depth", type=int, required=True)
    parser.add_argument("--relaxed", action="store_true")
    parser_args = parser.parse_args()

    driver = Driver()
    ol_l2_cpu2 = driver.analyze(
        "tenspiler/c2taco/cpp/for_synthesis/darknet/ol_l2_cpu2.ll",
        "tenspiler/c2taco/cpp/for_synthesis/darknet/ol_l2_cpu2.loops",
        "ol_l2_cpu2",
        ol_l2_cpu2_target_lang,
        defaultdict(lambda: InvGrammar(ol_l2_cpu2_inv0_grammar, [])),
        ol_l2_cpu2_ps_grammar,
    )

    n = Int("n")
    pred = mlList(Int, "pred")
    truth = mlList(Int, "truth")

    driver.add_var_objects([n, pred, truth])
    driver.add_precondition(n >= 1)
    driver.add_precondition(pred.len() >= n)
    driver.add_precondition(truth.len() >= n)

    map_int_to_int_synth = get_map_int_to_int_synth()
    driver.fns_synths = [
        map_int_to_int_synth,
    ]

    ol_l2_cpu2(n, pred, truth)

    start_time = time.time()
    relaxed_suffix = "_relaxed" if parser_args.relaxed else ""
    depth_suffix = f"_depth{parser_args.depth}"
    driver.synthesize(
        filename=f"ol_l2_cpu2{depth_suffix}{relaxed_suffix}", rounds_to_guess=9
    )
    end_time = time.time()

    print(f"Synthesis took {end_time - start_time} seconds")
