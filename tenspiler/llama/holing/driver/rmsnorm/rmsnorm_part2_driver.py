from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tenspiler.tenspiler_common import (
    call_integer_sqrt,
    call_vec_elemwise_mul,
    call_vec_scalar_mul,
    vec_elemwise_mul,
    vec_scalar_mul,
)


def rmsnorm_part2_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [vec_scalar_mul, vec_elemwise_mul]


def rmsnorm_part2_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    ret_val = writes[0]
    input, weight, ss = reads
    vec = choose(input, weight)
    cons = choose(Int(1))
    int_var = choose(ss, input.len())
    scalar = cons // call_integer_sqrt(int_var // int_var + cons)
    return ret_val == call_vec_scalar_mul(scalar, call_vec_elemwise_mul(vec, vec))


def rmsnorm_part2_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    # Second loop
    input, weight, ss = reads
    out = writes[0]
    i = writes[1]
    cons = choose(Int(1))
    int_var = choose(ss, input.len())
    scalar = cons // call_integer_sqrt(int_var // int_var + cons)
    vec = choose(input[:i], weight[:i])
    return and_objects(
        i >= 0,
        i <= input.len(),
        out == call_vec_scalar_mul(scalar, call_vec_elemwise_mul(vec, vec)),
    )


if __name__ == "__main__":
    # Synthesize the second loop
    driver = Driver()
    rmsnorm_part2 = driver.analyze(
        llvm_filepath="tenspiler/llama/cpp/for_synthesis/rmsnorm/rmsnorm_part2.ll",
        loops_filepath="tenspiler/llama/cpp/for_synthesis/rmsnorm/rmsnorm_part2.loops",
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

    driver.synthesize(filename="rmsnorm_part2")
