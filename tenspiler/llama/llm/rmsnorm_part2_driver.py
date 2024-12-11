import time
from pathlib import Path

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Int, List
from tenspiler.llm.scripts.models import LLMModel
from tenspiler.llm.scripts.utils import SingleLoopInfo, get_args_for_invariants
from tenspiler.utils.synthesis_utils import run_llm_synthesis_algorithm

if __name__ == "__main__":
    start_time = time.time()
    driver = Driver()
    loop_info = SingleLoopInfo(
        loop_var=Int("i"),
        read_vars=[List(Int, "input"), List(Int, "weight"), Int("ss")],
        modified_vars=[List(Int, "output")],
    )
    output_var = List(Int, "output")
    inv_args = replace_args(
        args=get_args_for_invariants(loop_info), replace_args={"output": "agg.result"}
    )

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

    input_code = Path(
        f"tenspiler/llama/cpp/for_synthesis/rmsnorm/rmsnorm_part2.cc"
    ).read_text()

    run_llm_synthesis_algorithm(
        driver=driver,
        loop_info=loop_info,
        output_var=output_var,
        source_code=input_code,
        benchmark_name="rmsnorm_part2",
        llm_model=LLMModel.GPT,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
