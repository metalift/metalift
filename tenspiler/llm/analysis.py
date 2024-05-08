from typing import Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import FnDecl, FnDeclRecursive, Int, Matrix
from metalift.rosette_translator import generate_vars
from metalift.vc_util import and_objects
from tenspiler.constants import TENSPILER_FNS


def analyze_darken_blend_8(driver: Driver):
    darken_blend_8 = driver.analyze(
        llvm_filepath="tenspiler/blend/cpp/for_synthesis/darken_blend_8.ll",
        loops_filepath="tenspiler/blend/cpp/for_synthesis/darken_blend_8.loops",
        fn_name="darken_blend_8",
        target_lang_fn=[],
        inv_grammars={
            "darken_blend_8_inv0": InvGrammar(None, []),
            "darken_blend_8_inv1": InvGrammar(None, ["row", "agg.result"]),
        },
        ps_grammar=None,
    )

    base = Matrix(Int, "base")
    active = Matrix(Int, "active")
    driver.add_var_objects([base, active])

    # Add preconditions
    driver.add_precondition(base.len() > 1)
    driver.add_precondition(base.len() == active.len())
    driver.add_precondition(base[0].len() == active[0].len())

    darken_blend_8(base, active)


def verify_benchmark(
    benchmark_name: str,
    synthesized_fn_decls: list[Union[FnDecl, FnDeclRecursive]],
    list_bound: int = 2,
    bitwidth: int = 6,
) -> None:
    driver = Driver()

    if benchmark_name == "darken_blend_8":
        analyze_darken_blend_8(driver)
    else:
        raise ValueError(f"Unknown benchmark: {benchmark_name}")

    f = open(f"./synthesisLogs/verify_{benchmark_name}.rkt", "w")
    print(
        "#lang rosette\n"
        + '(require "./bounded.rkt")\n'
        + '(require "./utils.rkt")\n'
        + "(require rosette/lib/angelic rosette/lib/match rosette/lib/synthax)\n"
        + "(require rosette/solver/smt/bitwuzla)\n"
        + '(current-solver (bitwuzla #:path "/home/c/Desktop/research/ml/bitwuzla/build/src/main/bitwuzla" #:options (hash \':seed 0)))\n'
        + "\n",
        # + "(require rosette/solver/smt/z3)\n"
        # + "(current-solver (z3 #:options (hash ':random-seed 0)))\n"
        # + "\n",
        file=f,
    )
    # write dsl code
    for fn_decl in TENSPILER_FNS:
        print("\n", fn_decl.to_rosette(), "\n", file=f)

    # write ps and inv
    for fn_decl in synthesized_fn_decls:
        print("\n", fn_decl.to_rosette(), "\n", file=f)

    # Write variables
    vars = set(driver.var_tracker.all())
    var_decls, _ = generate_vars(vars, list_bound)
    print(var_decls, file=f)

    # Write bitwidth
    print(f"(current-bitwidth {bitwidth})", file=f)

    # Write assertions
    vc = and_objects(*driver.asserts).src.simplify()
    print("(define (assertions)\n (assert %s))\n" % vc.to_rosette(), file=f)
    print("(verify (assertions))", file=f)

    f.close()
