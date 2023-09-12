from typing import List

from metalift.frontend.llvm import Driver
from metalift.ir import (Add, Call, Choose, Eq, Expr, SetT, Int,
                         FnDeclRecursive, IntLit, Ite, Var)
from tests.python.utils.utils import codegen

def double(t):
    return Call("double", Int(), t)

def target_lang():
    x = Var("x", Int())
    double = FnDeclRecursive(
        "double", Int(), Add(x, x), x
    )
    return [double]

def inv_grammar(v: Var, writes: List[Var], reads: List[Var]) -> Expr:
    raise Exception("no invariant")

def ps_grammar(ret_val: Var, writes: List[Var], reads: List[Var]) -> Expr:
    inputS = reads[0]
    inputAdd = reads[1]
    inputValue = reads[2]
    outputVar = writes[0]

    emptySet = Call("set-create", SetT(Int()))

    intLit = Choose(IntLit(0), IntLit(1), IntLit(2), IntLit(3))
    intValue = Choose(inputValue, intLit)

    condition = Eq(inputAdd, intLit)

    setIn = Choose(inputS, emptySet, Call("set-singleton", SetT(Int()), intValue))

    setTransform = Choose(
        setIn,
        Call("set-union", SetT(Int()), setIn, setIn),
        Call("set-minus", SetT(Int()), setIn, setIn),
    )

    chosenTransform = Ite(condition, setTransform, setTransform)

    summary = Eq(outputVar, chosenTransform)
    return summary

if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        llvm_filepath="tests/llvm/set1.ll",
        loops_filepath="tests/llvm/set1.loops",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammar=inv_grammar,
        ps_grammar=ps_grammar
    )

    s = driver.variable("s", SetT(Int()))
    x = driver.variable("add", Int())
    y = driver.variable("value", Int())

    test(s, x, y)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))