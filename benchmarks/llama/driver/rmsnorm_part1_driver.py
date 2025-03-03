import time
from pathlib import Path

from llmlift_scripts.synthesis import (
    LLMModel,
    VerificationMethod,
    run_llm_synthesis_algorithm,
)
from llmlift_scripts.utils import SingleLoopInfo, get_inv_args
from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Int, List
from metalift.utils.tenspiler.constants import (
    TENSPILER_FN_NAME_TO_AXIOMS,
    TENSPILER_FNS,
)

if __name__ == "__main__":
    start_time = time.time()
    driver = Driver()
    loop_info = SingleLoopInfo(
        loop_var=Int("i"),
        read_vars=[List(Int, "input"), List(Int, "weight")],
        modified_vars=[Int("ss")],
    )
    output_var = Int("ss")
    inv_args = get_inv_args(loop_info)

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

    input_code = Path(
        f"tenspiler/llama/cpp/for_synthesis/rmsnorm/rmsnorm_part1.cc"
    ).read_text()

    run_llm_synthesis_algorithm(
        driver=driver,
        loop_info=loop_info,
        output_var=output_var,
        source_code=input_code,
        benchmark_name="rmsnorm_part1",
        llm_model=LLMModel.GPT,
        dsl_fns=TENSPILER_FNS,
        dsl_fn_name_to_axioms=TENSPILER_FN_NAME_TO_AXIOMS,
        verification_method=VerificationMethod.ROSETTE,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
