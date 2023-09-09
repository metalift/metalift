from typing import List
from metalift.frontend.python import Driver

from metalift.ir import Add, And, BoolLit, Call, Choose, Eq, Expr, FnDeclRecursive, Ge, Gt, Int, IntLit, Ite, Le, ListT, Lt, Sub, Var

from mypy.nodes import Statement

from tests.python.utils.utils import codegen

# We use test_abs instead of abs because abs is reserved in cvc5.
TEST_ABS_FN_NAME = "test_abs"
LIST_ABS_SUM_FN_NAME = "list_abs_sum"

def target_lang() -> List[FnDeclRecursive]:
    lst = Var("lst", ListT(Int()))
    list_abs_sum = FnDeclRecursive(
        LIST_ABS_SUM_FN_NAME,
        Int(),
        Ite(
            Ge(Call("list_length", Int(), lst), IntLit(1)),
            Add(
                Ite(
                    Lt(Call("list_get", Int(), lst, IntLit(0)), IntLit(0)),
                    Sub(IntLit(0), Call("list_get", Int(), lst, IntLit(0))),
                    Call("list_get", Int(), lst, IntLit(0))
                ),
                Call(
                    LIST_ABS_SUM_FN_NAME,
                    Int(),
                    Call("list_tail", ListT(Int()), lst, IntLit(1)),
                )
            ),
            IntLit(0)
        ),
        lst
    )
    return [list_abs_sum]

def ps_grammar(ret_val: Var, ast: Statement, writes: List[Var], reads: List[Var], in_scope: List[Var]) -> Expr:
    lst = reads[0]
    lst_sum = Call(
        LIST_ABS_SUM_FN_NAME,
        Int(),
        lst
    )
    return Eq(ret_val, lst_sum)

def inv_grammar(v: Var, ast: Statement, writes: List[Var], reads: List[Var], in_scope: List[Var]) -> Expr:
    # This grammar func could be called with v as one of [curr_el, i, sum], and we really only want to generate this grammar once.
    if v.name() != "sum":
        return BoolLit(True)
    # reads = [curr_el, i, lst, sum]
    # writes = [curr_el, i, sum]
    lst = reads[2]
    choose_write = Choose(*writes)
    int_lit = Choose(Sub(IntLit(0), IntLit(1)), IntLit(0), IntLit(1), IntLit(2))
    lst_length = Call(
        "list_length",
        Int(),
        lst
    )
    lst_sum = Call(
        LIST_ABS_SUM_FN_NAME,
        Int(),
        lst
    )
    lst_tail_sum = Call(
        LIST_ABS_SUM_FN_NAME,
        Int(),
        Call(
            "list_tail",
            Int(),
            lst,
            Add(choose_write, int_lit)
        )
    )
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
            Eq(Add(choose_write, lst_tail_sum), lst_sum),
            Eq(choose_write, lst_tail_sum)
        )
    )

if __name__ == "__main__":
    filename = "tests/python/list_abs_sum.py"

    driver = Driver()
    test = driver.analyze(filename, "test", target_lang, inv_grammar, ps_grammar)

    v1 = driver.variable("in_lst", ListT(Int()))

    test(v1)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))
