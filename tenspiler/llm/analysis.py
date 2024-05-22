from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Int, List, Matrix, Object, create_object


def _process_args(args: list[Object], replace_args: dict[str, str]) -> list[Object]:
    new_args: list[Object] = []
    for arg in args:
        arg_name = replace_args.get(arg.name(), arg.name())
        new_args.append(create_object(arg.type, arg_name))
    return new_args


def analyze_dissolve_blend_8(
    driver: Driver, inv_args: tuple[list[Object], list[Object]]
) -> None:
    inv0_args, inv1_args = inv_args
    replace_args = {"out": "agg.result"}
    inv0_args = _process_args(inv0_args, replace_args)
    inv1_args = _process_args(inv1_args, replace_args)
    inv0_grammar = InvGrammar(None, [], inv0_args)
    inv1_grammar = InvGrammar(None, [], inv1_args)
    dissolve_blend_8 = driver.analyze(
        llvm_filepath="tenspiler/blend/cpp/for_synthesis/dissolve_blend_8.ll",
        loops_filepath="tenspiler/blend/cpp/for_synthesis/dissolve_blend_8.loops",
        fn_name="dissolve_blend_8",
        target_lang_fn=[],
        inv_grammars={
            "dissolve_blend_8_inv0": inv0_grammar,
            "dissolve_blend_8_inv1": inv1_grammar,
        },
        ps_grammar=None,
    )

    base = Matrix(Int, "base")
    active = Matrix(Int, "active")
    opacity = Int("opacity")
    rand_cons = Int("rand_cons")
    driver.add_var_objects([base, active, opacity, rand_cons])

    # Add preconditions
    driver.add_precondition(base.len() > 1)
    driver.add_precondition(base.len() == active.len())
    driver.add_precondition(base[0].len() == active[0].len())

    dissolve_blend_8(base, active, opacity, rand_cons)


def analyze_blend_double_loop(
    driver: Driver, benchmark_name: str, inv_args: tuple[list[Object], list[Object]]
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
        inv_grammars={"normal_blend_8_inv0": InvGrammar(None, [], inv_args)},
        ps_grammar=None,
    )

    base_var = List(Int, "base")
    active_var = List(Int, "active")
    opacity_var = Int("opacity")
    driver.add_var_objects([base_var, active_var, opacity_var])
    driver.add_precondition(base_var.len() == active_var.len())
    driver.add_precondition(base_var.len() > 0)

    normal_blend_8(base_var, active_var, opacity_var)


def analyze_softmax_part1(driver: Driver, inv_args: list[Object]) -> None:
    inv_args = _process_args(inv_args, {})
    softmax_part1 = driver.analyze(
        llvm_filepath="tenspiler/llama/cpp/for_synthesis/softmax/softmax_part1.ll",
        loops_filepath="tenspiler/llama/cpp/for_synthesis/softmax/softmax_part1.loops",
        fn_name="softmax_part1",
        target_lang_fn=[],
        inv_grammars={"softmax_part1_inv0": InvGrammar(None, [], inv_args)},
        ps_grammar=None,
    )

    input_var = List(Int, "input")
    max_pos_var = Int("max_pos")
    driver.add_var_objects([input_var, max_pos_var])
    driver.add_precondition(input_var.len() > 0)
    driver.add_precondition(max_pos_var <= input_var.len())
    driver.add_precondition(max_pos_var >= 1)

    softmax_part1(input_var, max_pos_var)


def analyze_softmax_part2(driver: Driver, inv_args: list[Object]):
    inv_args = _process_args(inv_args, {"output": "agg.result"})
    softmax_part2 = driver.analyze(
        llvm_filepath="tenspiler/llama/cpp/for_synthesis/softmax/softmax_part2.ll",
        loops_filepath="tenspiler/llama/cpp/for_synthesis/softmax/softmax_part2.loops",
        fn_name="softmax_part2",
        target_lang_fn=[],
        inv_grammars={"softmax_part2_inv0": InvGrammar(None, [], inv_args)},
        ps_grammar=None,
    )

    input_var = List(Int, "input")
    max_pos_var = Int("max_pos")
    max_val_var = Int("max_val")
    driver.add_var_objects([input_var, max_pos_var, max_val_var])
    driver.add_precondition(input_var.len() > 0)
    driver.add_precondition(max_pos_var <= input_var.len())
    driver.add_precondition(max_pos_var >= 1)

    softmax_part2(input_var, max_pos_var, max_val_var)


def analyze_softmax_part3(driver: Driver, inv_args: list[Object]):
    inv_args = _process_args(inv_args, {})
    softmax_part3 = driver.analyze(
        llvm_filepath="tenspiler/llama/cpp/for_synthesis/softmax/softmax_part3.ll",
        loops_filepath="tenspiler/llama/cpp/for_synthesis/softmax/softmax_part3.loops",
        fn_name="softmax_part3",
        target_lang_fn=[],
        inv_grammars={
            "softmax_part3_inv0": InvGrammar(None, [], inv_args),
        },
        ps_grammar=None,
    )

    output_var = List(Int, "output")
    max_pos_var = Int("max_pos")
    driver.add_var_objects([output_var, max_pos_var])
    driver.add_precondition(output_var.len() > 0)
    driver.add_precondition(max_pos_var <= output_var.len())
    driver.add_precondition(max_pos_var >= 1)

    softmax_part3(output_var, max_pos_var)


def analyze_softmax_part4(driver: Driver, inv_args: list[Object]) -> None:
    inv_args = _process_args(inv_args, {"output": "agg.result"})
    softmax_part4 = driver.analyze(
        llvm_filepath="tenspiler/llama/cpp/for_synthesis/softmax/softmax_part4.ll",
        loops_filepath="tenspiler/llama/cpp/for_synthesis/softmax/softmax_part4.loops",
        fn_name="softmax_part4",
        target_lang_fn=[],
        inv_grammars={"softmax_part4_inv0": InvGrammar(None, [], inv_args)},
        ps_grammar=None,
    )

    unnormalized_output_var = List(Int, "unnormalized_output")
    max_pos_var = Int("max_pos")
    sum_var = Int("sum")
    driver.add_var_objects([unnormalized_output_var, max_pos_var, sum_var])
    driver.add_precondition(unnormalized_output_var.len() > 0)
    driver.add_precondition(max_pos_var <= unnormalized_output_var.len())
    driver.add_precondition(max_pos_var >= 1)

    softmax_part4(unnormalized_output_var, max_pos_var, sum_var)


def analyze_rmsnorm_part1(driver: Driver, inv_args: list[Object]) -> None:
    inv_args = _process_args(inv_args, {})
    rmsnorm_part1 = driver.analyze(
        llvm_filepath="tenspiler/llama/cpp/for_synthesis/rmsnorm/rmsnorm_part1.ll",
        loops_filepath="tenspiler/llama/cpp/for_synthesis/rmsnorm/rmsnorm_part1.loops",
        fn_name="rmsnorm_part1",
        target_lang_fn=[],
        inv_grammars={"rmsnorm_part1_inv0": InvGrammar(None, [], inv_args)},
        ps_grammar=None,
    )

    input_var = List(Int, "input")
    weight_var = List(Int, "weight")
    driver.add_var_objects([input_var, weight_var])
    driver.add_precondition(input_var.len() == weight_var.len())
    driver.add_precondition(input_var.len() > 0)

    rmsnorm_part1(input_var, weight_var)


def analyze_rmsnorm_part2(driver: Driver, inv_args: list[Object]) -> None:
    inv_args = _process_args(inv_args, {"output": "agg.result"})
    rmsnorm_part2 = driver.analyze(
        llvm_filepath="tenspiler/llama/cpp/for_synthesis/rmsnorm/rmsnorm_part2.ll",
        loops_filepath="tenspiler/llama/cpp/for_synthesis/rmsnorm/rmsnorm_part2.loops",
        fn_name="rmsnorm_part2",
        target_lang_fn=[],
        inv_grammars={"rmsnorm_part2_inv0": InvGrammar(None, [], inv_args)},
        ps_grammar=None,
    )

    input_var = List(Int, "input")
    weight_var = List(Int, "weight")
    ss = Int("ss")
    driver.add_var_objects([input_var, weight_var, ss])
    driver.add_precondition(input_var.len() == weight_var.len())
    driver.add_precondition(input_var.len() > 0)

    rmsnorm_part2(input_var, weight_var, ss)


def analyze_matmul(driver: Driver, inv_args: list[Object]) -> None:
    inv0_args, inv1_args = inv_args
    replace_args = {"output": "agg.result"}
    inv0_args = _process_args(inv0_args, replace_args)
    inv1_args = _process_args(inv1_args, replace_args)
    matmul = driver.analyze(
        llvm_filepath="tenspiler/llama/cpp/for_synthesis/matmul.ll",
        loops_filepath="tenspiler/llama/cpp/for_synthesis/matmul.loops",
        fn_name="matmul",
        target_lang_fn=[],
        inv_grammars={
            "matmul_inv0": InvGrammar(None, [], inv0_args),
            "matmul_inv1": InvGrammar(None, [], inv1_args),
        },
        ps_grammar=None,
    )

    weight_var = Matrix(Int, "weight")
    input_var = List(Int, "input")
    driver.add_var_objects([weight_var, input_var])
    driver.add_precondition(weight_var.len() > 0)
    driver.add_precondition(weight_var[0].len() > 0)
    driver.add_precondition(weight_var[0].len() == input_var.len())

    matmul(weight_var, input_var)


def analyze_transformer_part1(driver: Driver, inv_args: list[Object]) -> None:
    inv0_args, inv1_args = inv_args
    inv0_args = _process_args(inv0_args, {"attention": "agg.result"})
    inv1_args = _process_args(inv1_args, {"attention": "agg.result"})
    transformer_part1 = driver.analyze(
        llvm_filepath="tenspiler/llama/cpp/for_synthesis/transformer/transformer_part1.ll",
        loops_filepath="tenspiler/llama/cpp/for_synthesis/transformer/transformer_part1.loops",
        fn_name="transformer_part1",
        target_lang_fn=[],
        inv_grammars={
            "transformer_part1_inv0": InvGrammar(None, [], inv0_args),
            "transformer_part1_inv1": InvGrammar(None, [], inv1_args),
        },
        ps_grammar=None,
    )

    token_position_var = Int("token_position")
    head_var = Int("head")
    head_size_var = Int("head_size")
    key_cache_layer_var = Matrix(Int, "key_cache_layer")
    q_var = List(Int, "q")
    driver.add_var_objects(
        [token_position_var, head_var, head_size_var, key_cache_layer_var, q_var]
    )
    driver.add_precondition(token_position_var > 0)
    driver.add_precondition(key_cache_layer_var.len() > token_position_var)
    driver.add_precondition(head_var >= 0)
    driver.add_precondition(head_var <= q_var.len())
    driver.add_precondition(head_var <= key_cache_layer_var.len())
    driver.add_precondition(head_size_var > 0)
    driver.add_precondition(head_size_var <= q_var.len())
    driver.add_precondition(head_size_var <= key_cache_layer_var.len())
    driver.add_precondition(
        (head_var * head_size_var + head_size_var) < key_cache_layer_var[0].len()
    )
    driver.add_precondition((head_var * head_size_var + head_size_var) < q_var.len())

    transformer_part1(
        token_position_var,
        head_var,
        head_size_var,
        key_cache_layer_var,
        q_var,
    )


def analyze_transformer_part2(driver: Driver, inv_args: list[Object]) -> None:
    inv0_args, inv1_args = inv_args
    inv0_args = _process_args(inv0_args, {"xb": "agg.result"})
    inv1_args = _process_args(inv1_args, {"xb": "agg.result"})
    transformer_part2 = driver.analyze(
        llvm_filepath="tenspiler/llama/cpp/for_synthesis/transformer/transformer_part2.ll",
        loops_filepath="tenspiler/llama/cpp/for_synthesis/transformer/transformer_part2.loops",
        fn_name="transformer_part2",
        target_lang_fn=[],
        inv_grammars={
            "transformer_part2_inv0": InvGrammar(None, [], inv0_args),
            "transformer_part2_inv1": InvGrammar(None, [], inv1_args),
        },
        ps_grammar=None,
    )
    token_position_var = Int("token_position")
    head_var = Int("head")
    head_size_var = Int("head_size")
    key_cache_layer_var = Matrix(Int, "key_cache_layer")
    attention_var = List(Int, "attention")
    driver.add_var_objects(
        [
            token_position_var,
            head_var,
            head_size_var,
            key_cache_layer_var,
            attention_var,
        ]
    )
    driver.add_precondition(token_position_var > 0)

    driver.add_precondition(key_cache_layer_var.len() > 0)
    driver.add_precondition(key_cache_layer_var[0].len() > 0)
    driver.add_precondition(attention_var.len() > 0)
    driver.add_precondition(key_cache_layer_var.len() > token_position_var)
    driver.add_precondition(
        key_cache_layer_var[0].len() > head_var * head_size_var + head_size_var
    )
    driver.add_precondition(attention_var.len() > token_position_var)

    driver.add_precondition(head_var >= 0)
    driver.add_precondition(head_var <= attention_var.len())
    driver.add_precondition(head_size_var > 0)
    driver.add_precondition(head_size_var <= attention_var.len())

    transformer_part2(
        token_position_var, head_var, head_size_var, key_cache_layer_var, attention_var
    )


def analyze_transformer_part3(driver: Driver, inv_args: list[Object]) -> None:
    inv_args = _process_args(inv_args, {"output": "agg.result"})
    transformer_part3 = driver.analyze(
        llvm_filepath="tenspiler/llama/cpp/for_synthesis/transformer/transformer_part3.ll",
        loops_filepath="tenspiler/llama/cpp/for_synthesis/transformer/transformer_part3.loops",
        fn_name="transformer_part3",
        target_lang_fn=[],
        inv_grammars={"transformer_part3_inv0": InvGrammar(None, [], inv_args)},
        ps_grammar=None,
    )

    input_var = List(Int, "input")
    hidden_dim_var = Int("hidden_dim")

    driver.add_var_objects([input_var, hidden_dim_var])
    driver.add_precondition(hidden_dim_var >= 0)
    driver.add_precondition(input_var.len() >= hidden_dim_var)

    transformer_part3(input_var, hidden_dim_var)


def analyze_transformer_part4(driver: Driver, inv_args: list[Object]) -> None:
    inv_args = _process_args(inv_args, {"output": "agg.result"})
    transformer_part4 = driver.analyze(
        llvm_filepath="tenspiler/llama/cpp/for_synthesis/transformer/transformer_part4.ll",
        loops_filepath="tenspiler/llama/cpp/for_synthesis/transformer/transformer_part4.loops",
        fn_name="transformer_part4",
        target_lang_fn=[],
        inv_grammars={"transformer_part4_inv0": InvGrammar(None, [], inv_args)},
        ps_grammar=None,
    )

    input1_var = List(Int, "input1")
    input2_var = List(Int, "input2")
    hidden_dim_var = Int("hidden_dim")

    driver.add_var_objects([input1_var, input2_var, hidden_dim_var])
    driver.add_precondition(hidden_dim_var >= 0)
    driver.add_precondition(input1_var.len() >= hidden_dim_var)
    driver.add_precondition(input2_var.len() >= hidden_dim_var)

    transformer_part4(input1_var, input2_var, hidden_dim_var)
