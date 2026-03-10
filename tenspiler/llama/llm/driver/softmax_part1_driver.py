import time
from pathlib import Path

from llm.synthesis import LLMModel, VerificationMethod, run_llm_synthesis_algorithm
from llm.utils import SingleLoopInfo, get_inv_args, infer_single_loop_info_from_llvm
from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Int, create_object
from tenspiler.constants import TENSPILER_FN_NAME_TO_AXIOMS, TENSPILER_FNS
from tenspiler.tree_parser import find_root_node_from_file, make_input_variables


def recreate_loop_info_from_var_map(
    loop_info: SingleLoopInfo, var_map: dict
) -> SingleLoopInfo:
    """Recreate loop_info so read_vars and modified_vars use types from var_map (e.g. from var_tracker after VC)."""
    read_vars = [
        create_object(var_map[var.var_name()].type, var.var_name())
        if var.var_name() in var_map
        else var
        for var in loop_info.read_vars
    ]
    modified_vars = [
        create_object(var_map[var.var_name()].type, var.var_name())
        if var.var_name() in var_map
        else var
        for var in loop_info.modified_vars
    ]
    return SingleLoopInfo(
        loop_var=loop_info.loop_var,
        read_vars=read_vars,
        modified_vars=modified_vars,
    )


if __name__ == "__main__":
    start_time = time.time()
    driver = Driver()
    llvm_path = "tenspiler/llama/cpp/for_synthesis/softmax/softmax_part1.ll"
    loops_path = "tenspiler/llama/cpp/for_synthesis/softmax/softmax_part1.loops"

    # Induction variable name (still supplied manually), all other loop info
    # (modified/read vars) inferred automatically from the LLVM + loops files.
    loop_var = Int("i")
    loop_info = infer_single_loop_info_from_llvm(
        llvm_filepath=llvm_path,
        loops_filepath=loops_path,
        fn_name="softmax_part1",
        loop_var=loop_var,
        inv_index=0,
    )
    output_var = Int("max_val")
    inv_args = get_inv_args(loop_info)

    softmax_part1 = driver.analyze(
        llvm_filepath=llvm_path,
        loops_filepath=loops_path,
        fn_name="softmax_part1",
        target_lang_fn=[],
        inv_grammars={"softmax_part1_inv0": InvGrammar(None, [], inv_args)},
        ps_grammar=None,
    )

    cc_path = "tenspiler/llama/cpp/for_synthesis/softmax/softmax_part1.cc"
    root_node = find_root_node_from_file(cc_path)
    input_vars = make_input_variables(root_node, driver)
    input_var, max_pos_var = input_vars["input"], input_vars["max_pos"]
    driver.add_precondition(input_var.len() > 0)
    driver.add_precondition(max_pos_var <= input_var.len())
    driver.add_precondition(max_pos_var >= 1)

    softmax_part1(input_var, max_pos_var)

    variables = driver.var_tracker.all()
    var_map = {var.name(): var for var in variables}
    loop_info = recreate_loop_info_from_var_map(loop_info, var_map)

    input_code = Path(
        f"tenspiler/llama/cpp/for_synthesis/softmax/softmax_part1.cc"
    ).read_text()

    run_llm_synthesis_algorithm(
        driver=driver,
        loop_info=loop_info,
        output_var=output_var,
        source_code=input_code,
        benchmark_name="softmax_part1",
        llm_model=LLMModel.GPT,
        dsl_fns=TENSPILER_FNS,
        dsl_fn_name_to_axioms=TENSPILER_FN_NAME_TO_AXIOMS,
        verification_method=VerificationMethod.ROSETTE,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
