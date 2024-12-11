import time
from pathlib import Path

from llm.scripts.models import LLMModel
from llm.scripts.utils import SingleLoopInfo, get_inv_args
from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Int, List
from tenspiler.utils.synthesis_utils import run_llm_synthesis_algorithm

if __name__ == "__main__":
    start_time = time.time()
    driver = Driver()
    loop_info = SingleLoopInfo(
        loop_var=Int("i"),
        read_vars=[
            List(Int, "input1"),
            List(Int, "input2"),
            Int("hidden_dim"),
        ],
        modified_vars=[List(Int, "output")],
    )
    output_var = List(Int, "output")
    inv_args = replace_args(
        args=get_inv_args(loop_info), replace_args={"output": "agg.result"}
    )
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

    input_code = Path(
        f"tenspiler/llama/cpp/for_synthesis/transformer/transformer_part4.cc"
    ).read_text()

    run_llm_synthesis_algorithm(
        driver=driver,
        loop_info=loop_info,
        output_var=output_var,
        source_code=input_code,
        benchmark_name="transformer_part3",
        llm_model=LLMModel.GPT,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
