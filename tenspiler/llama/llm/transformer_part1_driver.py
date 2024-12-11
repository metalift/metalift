import time
from pathlib import Path

from llm.synthesis import DoubleLoopInfo, LLMModel, run_llm_synthesis_algorithm
from llm.utils import get_inv_args, replace_args
from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Int, List, Matrix
from tenspiler.constants import TENSPILER_FN_NAME_TO_AXIOMS, TENSPILER_FNS

if __name__ == "__main__":
    start_time = time.time()
    driver = Driver()
    loop_info = DoubleLoopInfo(
        outer_loop_var=Int("timestep"),
        inner_loop_var=Int("i"),
        outer_loop_read_vars=[
            Int("token_position"),
            Int("head"),
            Int("head_size"),
            List(Int, "q"),
            List(List[Int], "key_cache_layer"),
        ],
        inner_loop_read_vars=[
            Int("token_position"),
            Int("head"),
            Int("head_size"),
            List(Int, "q"),
            List(List[Int], "key_cache_layer"),
            Int("timestep"),
        ],
        outer_loop_modified_vars=[List(Int, "attention")],
        inner_loop_modified_vars=[List(Int, "attention"), Int("score")],
    )
    output_var = List(Int, "attention")
    inv_args = get_inv_args(loop_info)

    inv0_args, inv1_args = inv_args
    inv0_args = replace_args(args=inv0_args, replace_args={"attention": "agg.result"})
    inv1_args = replace_args(args=inv1_args, replace_args={"attention": "agg.result"})
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

    input_code = Path(
        f"tenspiler/llama/cpp/for_synthesis/transformer/transformer_part1.cc"
    ).read_text()

    run_llm_synthesis_algorithm(
        driver=driver,
        loop_info=loop_info,
        output_var=output_var,
        source_code=input_code,
        benchmark_name="transformer_part1",
        llm_model=LLMModel.GPT,
        dsl_fns=TENSPILER_FNS,
        dsl_fn_name_to_axioms=TENSPILER_FN_NAME_TO_AXIOMS,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
