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
        modified_vars=[List(Int, "out")],
        read_vars=[List(Int, "base"), List(Int, "active"), Int("opacity")],
    )
    output_var = List(Int, "out")

    inv_args = replace_args(
        args=get_inv_args(loop_info), replace_args={"out": "agg.result"}
    )
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

    input_code = Path(
        f"tenspiler/blend/cpp/for_synthesis/normal_blend_8.cc"
    ).read_text()

    run_llm_synthesis_algorithm(
        driver=driver,
        loop_info=loop_info,
        output_var=output_var,
        source_code=input_code,
        benchmark_name="normal_blend_8",
        llm_model=LLMModel.GPT,
        dsl_fns=TENSPILER_FNS,
        dsl_fn_name_to_axioms=TENSPILER_FN_NAME_TO_AXIOMS,
        verification_method=VerificationMethod.ROSETTE,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
