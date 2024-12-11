import time
from pathlib import Path

from llm.synthesis import LLMModel, VerificationMethod, run_llm_synthesis_algorithm
from llm.utils import SingleLoopInfo, get_inv_args, replace_args
from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Int, List
from tenspiler.constants import TENSPILER_FN_NAME_TO_AXIOMS, TENSPILER_FNS

if __name__ == "__main__":
    start_time = time.time()
    driver = Driver()
    loop_info = SingleLoopInfo(
        loop_var=Int("i"),
        read_vars=[List(Int, "input"), Int("hidden_dim")],
        modified_vars=[List(Int, "output")],
    )
    output_var = List(Int, "output")
    inv_args = replace_args(
        args=get_inv_args(loop_info), replace_args={"output": "agg.result"}
    )
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

    input_code = Path(
        f"tenspiler/llama/cpp/for_synthesis/transformer/transformer_part3.cc"
    ).read_text()

    run_llm_synthesis_algorithm(
        driver=driver,
        loop_info=loop_info,
        output_var=output_var,
        source_code=input_code,
        benchmark_name="transformer_part3",
        llm_model=LLMModel.GPT,
        dsl_fns=TENSPILER_FNS,
        dsl_fn_name_to_axioms=TENSPILER_FN_NAME_TO_AXIOMS,
        verification_method=VerificationMethod.ROSETTE,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
