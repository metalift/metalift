from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tenspiler.tenspiler_common import call_reduce_sum, reduce_sum


def softmax_part3_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [reduce_sum]


def softmax_part3_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    ret_val = writes[0]
    output, max_pos = reads
    vec = choose(output[:max_pos])
    return ret_val == call_reduce_sum(vec)


def softmax_part3_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    output, max_pos = reads
    i, sum = writes
    vec = choose(output[:i])

    return and_objects(i >= 0, i <= max_pos, sum == call_reduce_sum(vec))


if __name__ == "__main__":
    # Synthesize part 3
    driver = Driver()
    softmax_part3 = driver.analyze(
        llvm_filepath="tenspiler/llama/cpp/for_synthesis/softmax/softmax_part3.ll",
        loops_filepath="tenspiler/llama/cpp/for_synthesis/softmax/softmax_part3.loops",
        fn_name="softmax_part3",
        target_lang_fn=softmax_part3_target_lang,
        inv_grammars={
            "softmax_part3_inv0": InvGrammar(softmax_part3_inv0_grammar, []),
        },
        ps_grammar=softmax_part3_ps_grammar,
    )

    output_var = mlList(Int, "output")
    max_pos_var = Int("max_pos")
    driver.add_var_objects([output_var, max_pos_var])
    driver.add_precondition(output_var.len() > 0)
    driver.add_precondition(max_pos_var <= output_var.len())
    driver.add_precondition(max_pos_var >= 1)

    softmax_part3(output_var, max_pos_var)
    driver.synthesize(filename="softmax_part3")
