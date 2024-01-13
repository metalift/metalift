from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tests.llvm.hardlift.hardlift_common import (
    call_integer_sqrt,
    call_vec_elemwise_mul,
    call_vec_scalar_mul,
    vec_elemwise_mul,
    vec_scalar_mul,
)
from tests.python.utils.utils import codegen


def rmsnorm_part2_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [vec_scalar_mul, vec_elemwise_mul]


def rmsnorm_part2_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    ret_val = writes[0]
    input, weight, ss = reads
    vec = choose(input, weight)
    inv_ss = 1 // call_integer_sqrt(ss // input.len() + 1)
    return ret_val == call_vec_scalar_mul(inv_ss, call_vec_elemwise_mul(vec, vec))


def rmsnorm_part2_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    # Second loop
    input, weight, ss = reads
    out = writes[0]
    i = writes[1]
    inv_ss = 1 // call_integer_sqrt(ss // input.len() + 1)
    vec = choose(input[:i], weight[:i])
    return and_objects(
        i >= 0,
        i <= input.len(),
        out == call_vec_scalar_mul(inv_ss, call_vec_elemwise_mul(vec, vec)),
    )


if __name__ == "__main__":
    # Synthesize the second loop
    driver = Driver()
    rmsnorm_part2 = driver.analyze(
        llvm_filepath="tests/llvm/hardlift/llama/cpp/rmsnorm/rmsnorm_part2.ll",
        loops_filepath="tests/llvm/hardlift/llama/cpp/rmsnorm/rmsnorm_part2.loops",
        fn_name="rmsnorm_part2",
        target_lang_fn=rmsnorm_part2_target_lang,
        inv_grammars={
            "rmsnorm_part2_inv0": InvGrammar(rmsnorm_part2_inv0_grammar, []),
        },
        ps_grammar=rmsnorm_part2_ps_grammar,
    )

    input_var = mlList(Int, "input")
    weight_var = mlList(Int, "weight")
    ss = Int("ss")
    driver.add_var_objects([input_var, weight_var, ss])
    driver.add_precondition(input_var.len() == weight_var.len())
    driver.add_precondition(input_var.len() > 0)

    rmsnorm_part2(input_var, weight_var, ss)

    driver.synthesize(noVerify=True)

    print("\n\ngenerated code:" + rmsnorm_part2.codegen(codegen))
