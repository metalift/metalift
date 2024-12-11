import time
from pathlib import Path

from llm.synthesis import (
    DoubleLoopInfo,
    LLMModel,
    VerificationMethod,
    run_llm_synthesis_algorithm,
)
from llm.utils import get_inv_args, replace_args
from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Int, List, Matrix
from tenspiler.constants import TENSPILER_FN_NAME_TO_AXIOMS, TENSPILER_FNS

if __name__ == "__main__":
    start_time = time.time()
    driver = Driver()
    loop_info = DoubleLoopInfo(
        outer_loop_var=Int("row"),
        inner_loop_var=Int("col"),
        outer_loop_read_vars=[List(Int, "weight"), List(Int, "input")],
        inner_loop_read_vars=[
            List(Int, "weight"),
            List(Int, "input"),
            List(Int, "output"),
            Int("row"),
        ],
        outer_loop_modified_vars=[List(Int, "output")],
        inner_loop_modified_vars=[List(Int, "output"), Int("curr")],
    )
    output_var = List(Int, "output")
    inv_args = get_inv_args(loop_info)
    inv0_args, inv1_args = inv_args
    inv0_args = replace_args(args=inv0_args, replace_args={"output": "agg.result"})
    inv1_args = replace_args(args=inv1_args, replace_args={"output": "agg.result"})
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

    input_code = Path(f"tenspiler/llama/cpp/for_synthesis/matmul.cc").read_text()

    run_llm_synthesis_algorithm(
        driver=driver,
        loop_info=loop_info,
        output_var=output_var,
        source_code=input_code,
        benchmark_name="matmul",
        llm_model=LLMModel.GPT,
        dsl_fns=TENSPILER_FNS,
        dsl_fn_name_to_axioms=TENSPILER_FN_NAME_TO_AXIOMS,
        verification_method=VerificationMethod.ROSETTE,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
