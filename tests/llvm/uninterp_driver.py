from collections import defaultdict
from typing import List

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, Int, Object, call, fn_decl
from tests.python.utils.utils import codegen

# define an uninterpreted function in the target language that doesn't have a body
# it should have the same name as the uninterpreted fn that we don't want the VC generator
# to process in the source (otherwise why are you using an uninterpreted function?)
uninterp_fn_name = "uninterp"


def uninterp(x: Object, y: Object) -> Int:
    return call(uninterp_fn_name, Int, x, y)


def target_lang() -> List[FnDecl]:
    x = Int("x")
    y = Int("y")
    uninterp = fn_decl(uninterp_fn_name, Int, None, x, y)
    return [uninterp]


def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    ret_val = writes[0]
    x, y = reads
    return ret_val == uninterp(x, x) + uninterp(y, y)


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    raise Exception("no loop in the source")


if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        llvm_filepath="tests/llvm/uninterp.ll",
        loops_filepath="tests/llvm/uninterp.loops",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammars=defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar=ps_grammar,
    )

    i = Int("i")
    j = Int("j")
    driver.add_var_objects([i, j])

    test(i, j, uninterp_fns=[uninterp_fn_name])

    driver.synthesize(filename="uninterp", uninterp_fns=[uninterp_fn_name])
    print("\n\ngenerated code:" + test.codegen(codegen))
