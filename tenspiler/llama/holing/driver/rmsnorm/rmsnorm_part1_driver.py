from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tenspiler.tenspiler_common import (
    call_reduce_sum,
    call_vec_elemwise_mul,
    reduce_sum,
    vec_elemwise_mul,
)


def rmsnorm_part1_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [vec_elemwise_mul, reduce_sum]


def rmsnorm_part1_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    ret_val = writes[0]
    input, weight = reads
    vec = choose(input, weight)
    return ret_val == call_reduce_sum(call_vec_elemwise_mul(vec, vec))


def rmsnorm_part1_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    # First loop
    input, weight = reads
    i, ss = writes
    vec = choose(input[:i], weight[:i])

    return and_objects(
        i >= 0, i <= input.len(), ss == call_reduce_sum(call_vec_elemwise_mul(vec, vec))
    )


if __name__ == "__main__":
    # Synthesize the first loop
    driver = Driver()
    rmsnorm_part1 = driver.analyze(
        llvm_filepath="tenspiler/llama/cpp/for_synthesis/rmsnorm/rmsnorm_part1.ll",
        loops_filepath="tenspiler/llama/cpp/for_synthesis/rmsnorm/rmsnorm_part1.loops",
        fn_name="rmsnorm_part1",
        target_lang_fn=rmsnorm_part1_target_lang,
        inv_grammars={
            "rmsnorm_part1_inv0": InvGrammar(rmsnorm_part1_inv0_grammar, []),
        },
        ps_grammar=rmsnorm_part1_ps_grammar,
    )

    input_var = mlList(Int, "input")
    weight_var = mlList(Int, "weight")
    driver.add_var_objects([input_var, weight_var])
    driver.add_precondition(input_var.len() == weight_var.len())
    driver.add_precondition(input_var.len() > 0)

    rmsnorm_part1(input_var, weight_var)
    driver.synthesize(filename="rmsnorm_part1")
