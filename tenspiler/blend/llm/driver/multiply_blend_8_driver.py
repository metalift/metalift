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
        outer_loop_read_vars=[
            List(List[Int], "base"),
            List(List[Int], "active"),
        ],
        inner_loop_read_vars=[
            List(List[Int], "base"),
            List(List[Int], "active"),
            Int("row"),
        ],
        outer_loop_modified_vars=[List(List[Int], "out")],
        inner_loop_modified_vars=[List(List[Int], "out"), List(Int, "row_vec")],
    )
    output_var = List(List[Int], "out")

    inv0_args, inv1_args = get_inv_args(loop_info)
    inv0_args = replace_args(args=inv0_args, replace_args={"out": "agg.result"})
    inv1_args = replace_args(args=inv1_args, replace_args={"out": "agg.result"})
    inv0_grammar = InvGrammar(None, [], inv0_args)
    inv1_grammar = InvGrammar(None, [], inv1_args)
    multiply_blend_8 = driver.analyze(
        llvm_filepath="tenspiler/blend/cpp/for_synthesis/multiply_blend_8.ll",
        loops_filepath="tenspiler/blend/cpp/for_synthesis/multiply_blend_8.loops",
        fn_name="multiply_blend_8",
        target_lang_fn=[],
        inv_grammars={
            "multiply_blend_8_inv0": inv0_grammar,
            "multiply_blend_8_inv1": inv1_grammar,
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

    multiply_blend_8(base, active)

    input_code = Path(
        f"tenspiler/blend/cpp/for_synthesis/multiply_blend_8.cc"
    ).read_text()

    run_llm_synthesis_algorithm(
        driver=driver,
        loop_info=loop_info,
        output_var=output_var,
        source_code=input_code,
        benchmark_name="multiply_blend_8",
        llm_model=LLMModel.GPT,
        dsl_fns=TENSPILER_FNS,
        dsl_fn_name_to_axioms=TENSPILER_FN_NAME_TO_AXIOMS,
        verification_method=VerificationMethod.ROSETTE,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
