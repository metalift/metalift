from collections import defaultdict
from typing import List

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, Int, Object, call, choose, fn_decl
from tests.python.utils.utils import codegen


def target_lang() -> List[FnDecl]:
    x = Int("x")
    y = Int("y")
    z = Int("z")
    fma = fn_decl("fma", Int, (x + y * z), x, y, z)
    return [fma]


# var := *reads | 0
# added := var + var
# var_or_fma := *reads | fma(added, added, added)
#
# return value := var_or_fma + var_or_fma
#
def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    ret_val = writes[0]
    var = choose(*reads, Int(0))
    added = var + var
    fma_call_object = call("fma", Int, added, added, added)
    var_or_fma = choose(*reads, fma_call_object)

    return ret_val == var_or_fma + var_or_fma


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    raise Exception("no loop in the source")


if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        llvm_filepath="tests/llvm/fma_dsl.ll",
        loops_filepath="tests/llvm/fma_dsl.loops",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammars=defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar=ps_grammar,
    )

    base = Int("base")
    arg1 = Int("arg1")
    base2 = Int("base2")
    arg2 = Int("arg2")
    driver.add_var_objects([base, arg1, base2, arg2])

    test(base, arg1, base2, arg2)

    driver.synthesize(filename="fma_dsl")

    print("\n\ngenerated code:" + test.codegen(codegen))
