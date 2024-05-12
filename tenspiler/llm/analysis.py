from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Int, Matrix


def analyze_blend_double_loop(driver: Driver, benchmark_name: str):
    benchmark = driver.analyze(
        llvm_filepath=f"tenspiler/blend/cpp/for_synthesis/{benchmark_name}.ll",
        loops_filepath=f"tenspiler/blend/cpp/for_synthesis/{benchmark_name}.loops",
        fn_name=benchmark_name,
        target_lang_fn=[],
        inv_grammars={
            f"{benchmark_name}_inv0": InvGrammar(None, []),
            f"{benchmark_name}_inv1": InvGrammar(None, ["row", "agg.result"]),
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

    benchmark(base, active)
