import time

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, FnDeclRecursive, Int, Object, fn_decl_recursive, ite, call
from metalift.vc_util import and_objects
from metalift.ir import Int, List as mlList
from collections import defaultdict
# from tests.llvm.gaudi.gaudi_common import ()
from typing import List, Union
from tests.python.utils.utils import codegen

ARG_MAX_FN_NAME = "argmax_fn"

def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    values = mlList[Int](Int, "values")
    # next_ind = call(
    #                 ARG_MAX_FN_NAME,
    #                 Int,
    #                 lst[1:]
    #             ) + 1
    argmax_fn = fn_decl_recursive(
        ARG_MAX_FN_NAME,
        Int,
        ite(
            values.len() > 1,
            ite(
                values[(call(ARG_MAX_FN_NAME, Int, values[1:]) + 1)] < values[0],
                Int(0),
                (call(ARG_MAX_FN_NAME, Int, values[1:]) + 1)
            ),
            Int(0)
        )
    )
    return [argmax_fn]

def ps_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    values = reads[0]
    ret_val = writes[0]
    argmax_val = call(
        ARG_MAX_FN_NAME,
        Int,
        values
    )
    return argmax_val == ret_val


def inv_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    values = reads[0]
    agg_result = writes[0]
    i = writes[1]
    return and_objects(
        i >= 0,
        i <= values.len(),
        agg_result == call(ARG_MAX_FN_NAME, Int, values[:i])
    )

if __name__ == "__main__":
    driver = Driver()
    argmax = driver.analyze(
        llvm_filepath="tests/llvm/gaudi/argmax.ll",
        loops_filepath="tests/llvm/gaudi/argmax.loops",
        fn_name="argmax",
        target_lang_fn=target_lang,
        inv_grammars=defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar=ps_grammar
    )

    values = mlList[Int](Int, "values")
    driver.add_var_objects([values])

    # Add preconditions
    driver.add_precondition(values.len() > 0)

    # driver.fns_synths = [all_possible_selects_two_args_synth]
    argmax(values)

    start_time = time.time()
    driver.synthesize(noVerify=True)
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
    print("\n\ngenerated code:" + argmax.codegen(codegen))