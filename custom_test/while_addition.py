from collections import defaultdict
from typing import List

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDeclRecursive, Int, Object, call, ite, fn_decl_recursive
from tests.python.utils.utils import codegen

def target_lang() -> List[FnDeclRecursive]:
    x = Int("x")
    y = Int("y")
    while_add = fn_decl_recursive(
        "while_add",
        Int,
        ite(
            x < y,
            call("while_add", Int, x + 1, y - 1),
            x
        ),
        x, y
    )
    return [while_add]

def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    ret_val = writes[0]
    candidate = call("while_add", Int, reads[0], reads[1])
    return ret_val == candidate

def trivial_inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    return Bool(True)

inv_grammar_dict = defaultdict(lambda: InvGrammar(trivial_inv_grammar, []))
inv_grammar_dict["while_addition_inv0"] = InvGrammar(trivial_inv_grammar, [])

if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        llvm_filepath="/Users/taeyoungkim/metalift/custom_test/while_addition.ll",
        loops_filepath="/Users/taeyoungkim/metalift/custom_test/while_addition.loops",
        fn_name="while_addition", 
        target_lang_fn=target_lang,
        inv_grammars=inv_grammar_dict,
        ps_grammar=ps_grammar,
    )
    
    x = Int("x")
    y = Int("y")
    driver.add_var_objects([x, y])
    
    test(x, y)
    
    driver.synthesize(filename="while_addition")
    
    print("\n\ngenerated code:" + test.codegen(codegen))
