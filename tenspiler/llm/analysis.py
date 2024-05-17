from collections import defaultdict
from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Int, List, Matrix, Object, Var, create_object


def _process_args(args: list[Object], replace_args: dict[str, str]) -> list[Object]:
    new_args: list[Object] = []
    for arg in args:
        arg_name = replace_args.get(arg.name(), arg.name())
        new_args.append(create_object(arg.type, arg_name))
    return new_args

def analyze_blend_double_loop(
    driver: Driver,
    benchmark_name: str,
    inv_args: tuple[list[Object], list[Object]]
):
    inv0_args, inv1_args = inv_args
    replace_args = {"out": "agg.result"}
    inv0_args = _process_args(inv0_args, replace_args)
    inv1_args = _process_args(inv1_args, replace_args)
    inv0_grammar = InvGrammar(None, [], inv0_args)
    inv1_grammar = InvGrammar(None, [], inv1_args)
    benchmark = driver.analyze(
        llvm_filepath=f"tenspiler/blend/cpp/for_synthesis/{benchmark_name}.ll",
        loops_filepath=f"tenspiler/blend/cpp/for_synthesis/{benchmark_name}.loops",
        fn_name=benchmark_name,
        target_lang_fn=[],
        inv_grammars={
            f"{benchmark_name}_inv0": inv0_grammar,
            f"{benchmark_name}_inv1": inv1_grammar,
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

def analyze_normal_blend_f(driver: Driver, inv_args: list):
    inv_args = _process_args(inv_args, {"out": "agg.result"})
    normal_blend_f = driver.analyze(
        "tenspiler/blend/cpp/for_synthesis/normal_blend_f.ll",
        "tenspiler/blend/cpp/for_synthesis/normal_blend_f.loops",
        "normal_blend_f",
        target_lang_fn=[],
        inv_grammars={"normal_blend_f_inv0": InvGrammar(None, [], inv_args)},
        ps_grammar=None,
    )

    base_var = List(Int, "base")
    active_var = List(Int, "active")
    opacity_var = Int("opacity")
    driver.add_var_objects([base_var, active_var, opacity_var])
    driver.add_precondition(base_var.len() == active_var.len())
    driver.add_precondition(base_var.len() > 0)

    normal_blend_f(base_var, active_var, opacity_var)

def analyze_normal_blend_8(driver: Driver, inv_args: list[Object]):
    inv_args = _process_args(inv_args, {"out": "agg.result"})
    normal_blend_8 = driver.analyze(
        "tenspiler/blend/cpp/for_synthesis/normal_blend_8.ll",
        "tenspiler/blend/cpp/for_synthesis/normal_blend_8.loops",
        "normal_blend_8",
        target_lang_fn=[],
        inv_grammars=defaultdict(lambda: InvGrammar(None, [], inv_args)),
        ps_grammar=None,
    )

    base_var = List(Int, "base")
    active_var = List(Int, "active")
    opacity_var = Int("opacity")
    driver.add_var_objects([base_var, active_var, opacity_var])
    driver.add_precondition(base_var.len() == active_var.len())
    driver.add_precondition(base_var.len() > 0)

    normal_blend_8(base_var, active_var, opacity_var)