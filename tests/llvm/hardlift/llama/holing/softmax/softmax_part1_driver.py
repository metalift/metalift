from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tests.llvm.hardlift.hardlift_common import call_reduce_max, reduce_max


def softmax_part1_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [reduce_max]

def softmax_part1_ps_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    ret_val = writes[0]
    input, max_pos = reads
    vec = choose(input[:max_pos])
    return ret_val == call_reduce_max(vec)

def softmax_part1_inv0_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    input, max_pos = reads
    i, max_val = writes
    vec = input[:i]
    return and_objects(
        i >= 1,
        i <= max_pos,
        max_val == call_reduce_max(vec)
    )

def softmax_part1_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [reduce_max]


if __name__ == "__main__":
    # Synthesize part 1
    driver = Driver()
    softmax_part1 = driver.analyze(
        llvm_filepath="tests/llvm/hardlift/llama/cpp/softmax/softmax_part1.ll",
        loops_filepath="tests/llvm/hardlift/llama/cpp/softmax/softmax_part1.loops",
        fn_name="softmax_part1",
        target_lang_fn=softmax_part1_target_lang,
        inv_grammars={
            "softmax_part1_inv0": InvGrammar(softmax_part1_inv0_grammar, []),
        },
        ps_grammar=softmax_part1_ps_grammar
    )

    input_var = mlList(Int, "input")
    max_pos_var = Int("max_pos")
    driver.add_var_objects([input_var, max_pos_var])
    driver.add_precondition(input_var.len() > 0)
    driver.add_precondition(max_pos_var <= input_var.len())
    driver.add_precondition(max_pos_var >= 1)

    softmax_part1(input_var, max_pos_var)
    driver.synthesize(noVerify=True)
