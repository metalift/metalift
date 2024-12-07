import time
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tenspiler.axioms import vec_elemwise_mul_axiom
from tenspiler.codegen.utils import DataType
from tenspiler.tenspiler_common import call_vec_elemwise_mul, vec_elemwise_mul
from tenspiler.utils.synthesis_utils import run_synthesis_algorithm


def transformer_part4_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [vec_elemwise_mul, vec_elemwise_mul_axiom]


def transformer_part4_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    ret_val = writes[0]
    input1, input2, hidden_dim = reads
    vec = choose(input1[:hidden_dim], input2[:hidden_dim])
    return ret_val == call_vec_elemwise_mul(vec, vec)


def transformer_part4_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    input1, input2, hidden_dim = reads
    out, i, _ = writes
    vec = choose(
        input1[:i],
        input2[:i],
    )

    return and_objects(i >= 0, i <= hidden_dim, out == call_vec_elemwise_mul(vec, vec))


if __name__ == "__main__":
    driver = Driver()
    transformer_part4 = driver.analyze(
        llvm_filepath="tenspiler/llama/cpp/for_synthesis/transformer/transformer_part4.ll",
        loops_filepath="tenspiler/llama/cpp/for_synthesis/transformer/transformer_part4.loops",
        fn_name="transformer_part4",
        target_lang_fn=transformer_part4_target_lang,
        inv_grammars={
            "transformer_part4_inv0": InvGrammar(transformer_part4_inv0_grammar, [])
        },
        ps_grammar=transformer_part4_ps_grammar,
    )

    input1_var = mlList(Int, "input1")
    input2_var = mlList(Int, "input2")
    hidden_dim_var = Int("hidden_dim")

    driver.add_var_objects([input1_var, input2_var, hidden_dim_var])
    driver.add_precondition(hidden_dim_var >= 0)
    driver.add_precondition(input1_var.len() >= hidden_dim_var)
    driver.add_precondition(input2_var.len() >= hidden_dim_var)

    start_time = time.time()
    transformer_part4(input1_var, input2_var, hidden_dim_var)
    run_synthesis_algorithm(
        driver=driver,
        data_type=DataType.FLOAT,
        benchmark_name="transformer_part4",
        has_relaxed=False,
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
