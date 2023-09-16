from collections import defaultdict
from typing import List

from metalift.frontend.llvm import Driver
from metalift.ir import Call, Choose, Eq, Expr, FnDecl, Int, IntLit, IntObject, Var
from tests.python.utils.utils import codegen

def target_lang() -> List[FnDecl]:
    x = IntObject("x")
    y = IntObject("y")
    z = IntObject("z")
    fma = FnDecl("fma", Int(), x + y * z, x, y, z)
    return [fma]


# var := *reads | 0
# added := var + var
# var_or_fma := *reads | fma(added, added, added)
#
# return value := var_or_fma + var_or_fma
#
def ps_grammar(ret_val: Var, writes: List[Var], reads: List[Var]) -> Expr:
    var = Choose(*reads, IntObject(0))
    added = var + var
    fma_call_object = call("fma", Int, added, added, added)
    var_or_fma = choose(*reads, fma_call_object)

    return ret_val == var_or_fma + var_or_fma

def inv_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    raise Exception("no loop in the source")


if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        llvm_filepath="tests/llvm/fma_dsl.ll",
        loops_filepath="tests/llvm/fma_dsl.loops",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammars=defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar=ps_grammar
    )

    base = IntObject("base")
    arg1 = IntObject("arg1")
    base2 = IntObject("base2")
    arg2 = IntObject("arg2")

    test(base, arg1, base2, arg2)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))