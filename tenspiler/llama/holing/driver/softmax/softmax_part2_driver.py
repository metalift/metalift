from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, choose
from metalift.vc_util import and_objects
from tenspiler.tenspiler_common import (
    call_vec_map,
    call_vec_scalar_sub,
    get_map_int_to_int_synth,
    map_int_to_int,
    map_int_to_int_fn_obj,
    vec_map,
    vec_scalar_sub,
)


def softmax_part2_target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    return [vec_scalar_sub, vec_map, map_int_to_int]


def softmax_part2_ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    ret_val = writes[0]
    input, max_pos, max_val = reads
    int_var = choose(max_pos, max_val)
    vec = choose(input[:max_pos])
    return ret_val == call_vec_map(
        call_vec_scalar_sub(int_var, vec), map_int_to_int_fn_obj
    )


def softmax_part2_inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    input, max_pos, max_val = reads
    out, cur, i = writes
    int_var = choose(max_pos, max_val)
    vec = choose(input[:i])

    return and_objects(
        i >= 0,
        i <= max_pos,
        out == call_vec_map(call_vec_scalar_sub(int_var, vec), map_int_to_int_fn_obj),
    )


if __name__ == "__main__":
    # Synthesize part 2
    driver = Driver()
    softmax_part2 = driver.analyze(
        llvm_filepath="tenspiler/llama/cpp/for_synthesis/softmax/softmax_part2.ll",
        loops_filepath="tenspiler/llama/cpp/for_synthesis/softmax/softmax_part2.loops",
        fn_name="softmax_part2",
        target_lang_fn=softmax_part2_target_lang,
        inv_grammars={
            "softmax_part2_inv0": InvGrammar(softmax_part2_inv0_grammar, []),
        },
        ps_grammar=softmax_part2_ps_grammar,
    )

    input_var = mlList(Int, "input")
    max_pos_var = Int("max_pos")
    max_val_var = Int("max_val")
    driver.add_var_objects([input_var, max_pos_var, max_val_var])
    driver.add_precondition(input_var.len() > 0)
    driver.add_precondition(max_pos_var <= input_var.len())
    driver.add_precondition(max_pos_var >= 1)

    softmax_part2(input_var, max_pos_var, max_val_var)
    map_int_to_int_synth = get_map_int_to_int_synth()
    driver.fns_synths = [map_int_to_int_synth]
    driver.synthesize(filename="softmax_part2", no_verify=True)
