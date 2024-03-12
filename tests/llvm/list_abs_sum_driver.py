from collections import defaultdict
from typing import List

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, Expr, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Object, call, choose, fn_decl_recursive, ite
from metalift.vc_util import and_objects
from tests.python.utils.utils import codegen

# We use test_abs instead of abs because abs is reserved in cvc5.
TEST_ABS_FN_NAME = "test_abs"
LIST_ABS_SUM_FN_NAME = "list_abs_sum"


def target_lang() -> List[FnDeclRecursive]:
    lst = mlList(Int, "lst")
    list_abs_sum = fn_decl_recursive(
        LIST_ABS_SUM_FN_NAME,
        Int,
        ite(
            lst.len() >= 1,
            ite(lst[0] < 0, Int(0) - lst[0], lst[0])
            + call(LIST_ABS_SUM_FN_NAME, Int, lst[1:]),
            Int(0),
        ),
        lst,
    )
    return [list_abs_sum]


def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    ret_val = writes[0]
    lst = reads[0]
    lst_sum = call(LIST_ABS_SUM_FN_NAME, Int, lst)
    return ret_val == lst_sum


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Expr:
    lst = reads[0]
    choose_write = choose(*writes)

    int_lit = choose(Int(0) - Int(1), Int(0), Int(1), Int(2))
    lst_length = lst.len()

    lst_sum = call(LIST_ABS_SUM_FN_NAME, Int, lst)
    lst_tail_sum = call(LIST_ABS_SUM_FN_NAME, Int, lst[choose_write + int_lit :])

    index_lower_bound = choose(
        choose_write >= int_lit,
        choose_write > int_lit,
    )
    index_upper_bound = choose(
        choose_write <= lst_length,
        choose_write < lst_length,
    )
    return and_objects(
        index_lower_bound,
        index_upper_bound,
        choose(choose_write + lst_tail_sum == lst_sum, choose_write == lst_tail_sum),
    )


if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        llvm_filepath="tests/llvm/list_abs_sum.ll",
        loops_filepath="tests/llvm/list_abs_sum.loops",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammars=defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar=ps_grammar,
    )

    lst = mlList(Int, "lst")
    driver.add_var_object(lst)

    test(lst)

    driver.synthesize(filename="list_abs_sum")

    print("\n\ngenerated code:" + test.codegen(codegen))
