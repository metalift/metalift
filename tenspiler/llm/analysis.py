from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Int, Matrix


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
