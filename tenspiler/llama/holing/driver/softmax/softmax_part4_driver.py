import time
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tenspiler.axioms import vec_scalar_div_axiom
from tenspiler.codegen.utils import DataType
from tenspiler.tenspiler_common import call_vec_scalar_div, vec_scalar_div
from tenspiler.utils.synthesis_utils import run_synthesis_algorithm


def softmax_part4_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [vec_scalar_div, vec_scalar_div_axiom]


def softmax_part4_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    ret_val = writes[0]
    unnormalized_output, max_pos, sum = reads
    vec = choose(unnormalized_output[:max_pos])
    return ret_val == call_vec_scalar_div(sum, vec)


def softmax_part4_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    unnormalized_output, max_pos, sum = reads
    out, i, _ = writes
    vec = choose(unnormalized_output[:i], unnormalized_output[:1])

    return and_objects(i >= 0, i <= max_pos, out == call_vec_scalar_div(sum, vec))


if __name__ == "__main__":
    # Synthesize part 4
    driver = Driver()
    softmax_part4 = driver.analyze(
        llvm_filepath="tenspiler/llama/cpp/for_synthesis/softmax/softmax_part4.ll",
        loops_filepath="tenspiler/llama/cpp/for_synthesis/softmax/softmax_part4.loops",
        fn_name="softmax_part4",
        target_lang_fn=softmax_part4_target_lang,
        inv_grammars={
            "softmax_part4_inv0": InvGrammar(softmax_part4_inv0_grammar, []),
        },
        ps_grammar=softmax_part4_ps_grammar,
    )

    unnormalized_output_var = mlList(Int, "unnormalized_output")
    max_pos_var = Int("max_pos")
    sum_var = Int("sum")
    driver.add_var_objects([unnormalized_output_var, max_pos_var, sum_var])
    driver.add_precondition(unnormalized_output_var.len() > 0)
    driver.add_precondition(max_pos_var <= unnormalized_output_var.len())
    driver.add_precondition(max_pos_var >= 1)

    start_time = time.time()
    softmax_part4(unnormalized_output_var, max_pos_var, sum_var)
    run_synthesis_algorithm(
        driver=driver,
        data_type=DataType.FLOAT,
        benchmark_name="softmax_part4",
        has_relaxed=False,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
