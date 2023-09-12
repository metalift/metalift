from typing import List

from metalift.frontend.llvm import Driver
from metalift.ir import Call, Choose, Eq, Expr, FnDecl, Int, IntLit, Var
from tests.python.utils.utils import codegen


def target_lang() -> List[FnDecl]:
    x = Var("x", Int())
    y = Var("y", Int())
    z = Var("z", Int())
    fma = FnDecl("fma", Int(), x + y * z, x, y, z)
    return [fma]


# var := *reads | 0
# added := var + var
# var_or_fma := *reads | fma(added, added, added)
#
# return value := var_or_fma + var_or_fma
#
def ps_grammar(ret_val: Var, writes: List[Var], reads: List[Var]) -> Expr:
    var = Choose(*reads, IntLit(0))
    added = var + var
    var_or_fma = Choose(*reads, Call("fma", Int(), added, added, added))

    return Eq(ret_val, var_or_fma + var_or_fma)

def inv_grammar(v: Var, writes: List[Var], reads: List[Var]) -> Expr:
    raise Exception("no loop in the source")


if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        llvm_filepath="tests/llvm/fma_dsl.ll",
        loops_filepath="tests/llvm/fma_dsl.loops",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammar=inv_grammar,
        ps_grammar=ps_grammar
    )

    v1 = driver.variable("base", Int())
    v2 = driver.variable("arg1", Int())
    v3 = driver.variable("base2", Int())
    v4 = driver.variable("arg2", Int())

    test(v1, v2, v3, v4)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))