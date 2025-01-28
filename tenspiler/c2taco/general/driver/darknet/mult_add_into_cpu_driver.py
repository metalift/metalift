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


def mult_add_into_cpu_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [
        *vec_vec_to_vec_target_lang,
        *scalar_vec_to_vec_target_lang,
        *vec_to_vec_target_lang,
        *vec_to_int_target_lang,
    ]


def mult_add_into_cpu_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    N, X, Y, Z = reads
    out = writes[0]
    int_var = choose(Int(0), N).maybe_relaxed(parser_args.relaxed)
    slice_index = get_int_expr_eq_or_below_depth(int_var, depth=parser_args.depth)
    vec = choose(X, Y, Z)
    vec = vec[slice_index:slice_index]
    vec = get_matrix_or_vec_expr_eq_or_below_depth(
        vec, int_var=int_var, depth=parser_args.depth
    )
    return out == vec


def mult_add_into_cpu_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    N, X, Y, Z = reads
    out, i, _ = writes
    lower_bound = Int(0)
    upper_bound = N
    int_var = choose(lower_bound, upper_bound, i).maybe_relaxed(parser_args.relaxed)
    slice_index = get_int_expr_eq_or_below_depth(int_var, parser_args.depth)
    vec = choose(X, Y, Z)
    vec = vec[slice_index:slice_index]
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
    mult_add_into_cpu = driver.analyze(
        "tenspiler/c2taco/cpp/for_synthesis/darknet/mult_add_into_cpu.ll",
        "tenspiler/c2taco/cpp/for_synthesis/darknet/mult_add_into_cpu.loops",
        "mult_add_into_cpu",
        mult_add_into_cpu_target_lang,
        defaultdict(lambda: InvGrammar(mult_add_into_cpu_inv0_grammar, [])),
        mult_add_into_cpu_ps_grammar,
    )

    N = Int("N")
    X = mlList(Int, "X")
    Y = mlList(Int, "Y")
    Z = mlList(Int, "Z")

    driver.add_var_objects([N, X, Y, Z])
    driver.add_precondition(N >= 1)
    driver.add_precondition(X.len() >= N)
    driver.add_precondition(Y.len() >= N)
    driver.add_precondition(Z.len() >= N)
    map_int_to_int_synth = get_map_int_to_int_synth()
    driver.fns_synths = [
        map_int_to_int_synth,
    ]

    mult_add_into_cpu(N, X, Y, Z)

    start_time = time.time()
    relaxed_suffix = "_relaxed" if parser_args.relaxed else ""
    depth_suffix = f"_depth{parser_args.depth}"
    driver.synthesize(filename=f"mult_add_into_cpu{depth_suffix}{relaxed_suffix}")
    end_time = time.time()

    print(f"Synthesis took {end_time - start_time} seconds")
