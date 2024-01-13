from typing import List
from metalift.frontend.python import Driver

from metalift.ir import (
    Add,
    And,
    Bool,
    Call,
    Choose,
    Eq,
    Expr,
    FnDeclRecursive,
    Ge,
    Gt,
    Int,
    Ite,
    Le,
    List as mlList,
    Lt,
    Var,
)

from tests.python.utils.utils import codegen

# We use test_abs instead of abs because abs is reserved in cvc5.
TEST_ABS_FN_NAME = "test_abs"
LIST_ABS_SUM_FN_NAME = "list_abs_sum"


def target_lang() -> List[FnDeclRecursive]:
    lst = mlList[Int](Int, "lst")
    list_abs_sum = FnDeclRecursive(
        LIST_ABS_SUM_FN_NAME,
        Int,
        Ite(
            lst.len() >= 1,
            Add(
                Ite(lst[0] < 0, Int(0) - lst[0], lst[0]),
                Call(LIST_ABS_SUM_FN_NAME, Int, lst[1:]),
            ),
            Int(0),
        ),
        lst,
    )
    return [list_abs_sum]


def ps_grammar(
    ret_val: Var, writes: List[Var], reads: List[Var], in_scope: List[Var]
) -> Expr:
    lst = reads[0]
    lst_sum = Call(LIST_ABS_SUM_FN_NAME, Int, lst)
    return Eq(ret_val, lst_sum)


def inv_grammar(
    v: Var, writes: List[Var], reads: List[Var], in_scope: List[Var]
) -> Expr:
    # This grammar func could be called with v as one of [curr_el, i, sum], and we really only want to generate this grammar once.
    if v.var_name() != "sum":
        return Bool(True)
    # reads = [curr_el, i, lst, sum]
    # writes = [curr_el, i, sum]
    lst = reads[2]
    choose_write = Choose(*writes)
    int_lit = Choose(Int(0) - Int(1), Int(0), Int(1), Int(2))
    lst_length = lst.len()
    lst_sum = Call(LIST_ABS_SUM_FN_NAME, Int, lst)
    lst_tail_sum = Call(LIST_ABS_SUM_FN_NAME, Int, lst[Add(choose_write, int_lit) :])
    index_lower_bound = Choose(
        Ge(choose_write, int_lit),
        Gt(choose_write, int_lit),
    )
    index_upper_bound = Choose(
        Le(choose_write, lst_length),
        Lt(choose_write, lst_length),
    )
    return And(
        And(index_lower_bound, index_upper_bound),
        Choose(
            Eq(Add(choose_write, lst_tail_sum), lst_sum), Eq(choose_write, lst_tail_sum)
        ),
    )


if __name__ == "__main__":
    filename = "tests/python/list_abs_sum.py"

    driver = Driver()
    test = driver.analyze(filename, "test", target_lang, inv_grammar, ps_grammar)

    lst = mlList[Int](Int, "lst")
    driver.add_var_object(lst)

    test(lst)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))
