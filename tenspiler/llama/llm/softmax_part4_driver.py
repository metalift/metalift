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
        modified_vars=[List(Int, "output")],
        read_vars=[
            List(Int, "unnormalized_output"),
            Int("max_pos"),
            Int("sum"),
        ],
    )
    output_var = List(Int, "output")
    inv_args = replace_args(
        args=get_inv_args(loop_info), replace_args={"output": "agg.result"}
    )

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

    input_code = Path(
        f"tenspiler/llama/cpp/for_synthesis/softmax/softmax_part4.cc"
    ).read_text()

    run_llm_synthesis_algorithm(
        driver=driver,
        loop_info=loop_info,
        output_var=output_var,
        source_code=input_code,
        benchmark_name="softmax_part4",
        llm_model=LLMModel.GPT,
        dsl_fns=TENSPILER_FNS,
        dsl_fn_name_to_axioms=TENSPILER_FN_NAME_TO_AXIOMS,
        verification_method=VerificationMethod.ROSETTE,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
