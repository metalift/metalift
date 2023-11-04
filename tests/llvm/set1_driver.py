from collections import defaultdict
from typing import List

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import (BoolObject, IntObject, NewObject, SetObject,
                         choose, ite, fnDeclRecursive)
from tests.python.utils.utils import codegen


def target_lang():
    x = IntObject("x")
    double = fnDeclRecursive(
        "double",
        IntObject,
        (x + x).src,
        x.src
    )
    return [double]

def inv_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> BoolObject:
    raise Exception("no invariant")

def ps_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> BoolObject:
    ret_val = writes[0]
    input_s = reads[0]
    input_add = reads[1]
    input_value = reads[2]
    output_var = writes[0]

    empty_set = SetObject.empty(IntObject)

    int_lit = choose(
        IntObject(0),
        IntObject(1),
        IntObject(2),
        IntObject(3)
    )
    int_value = choose(input_value, int_lit)

    condition = input_add == int_lit

    set_in = choose(
        input_s,
        empty_set,
        SetObject.singleton(int_value)
    )

    set_transform = choose(
        set_in,
        set_in.union(set_in),
        set_in.difference(set_in)
    )

    chosen_transform = ite(
        condition,
        set_transform,
        set_transform
    )

    summary = output_var == chosen_transform
    return summary

if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        llvm_filepath="tests/llvm/set1.ll",
        loops_filepath="tests/llvm/set1.loops",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammars=defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar=ps_grammar
    )

    s = SetObject(IntObject, "s")
    add = IntObject("add")
    value = IntObject("value")
    driver.add_var_objects([s, add, value])

    test(s, add, value)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))