from collections import defaultdict
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Axiom, Bool, Fn, FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import (
    Object,
    Synth,
    call,
    call_value,
    choose,
    fn_decl,
    fn_decl_recursive,
    implies,
    ite,
)
from metalift.vc_util import and_objects
from tests.python.utils.utils import codegen

# We need to define some global variables as they need to persist across function calls
LM_NAME = "lm"
LR_NAME = "lr"
val = Int("val")
val2 = Int("val2")


def fns_synths() -> List[Synth]:
    lm_synth = Synth(LM_NAME, choose(Int(0), Int(1), Int(2), Int(3)).src, val.src)
    v = choose(val, val2)
    lr_synth = Synth(LR_NAME, choose(v + v, v - v, v * v).src, val.src, val2.src)
    return [lm_synth, lr_synth]


def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    in_lst = mlList(Int, "in_lst")
    lm_fn = Fn((Int, Int), "f")
    lr_fn = Fn((Int, Int, Int), "f")

    mapper = fn_decl(LM_NAME, Int, None, val)
    reducer = fn_decl(LR_NAME, Int, None, val, val2)

    map_fn = fn_decl_recursive(
        "map",
        mlList[Int],
        ite(
            in_lst.len() == 0,
            mlList.empty(Int),
            call("map", mlList[Int], in_lst[1:], lm_fn).prepend(
                call_value(lm_fn, in_lst[0])
            ),
        ),
        in_lst,
        lm_fn,
    )

    reduce_fn = fn_decl_recursive(
        "reduce",
        Int,
        ite(
            in_lst.len() == 0,
            Int(0),
            call_value(lr_fn, in_lst[0], call("reduce", Int, in_lst[1:], lr_fn)),
        ),
        in_lst,
        lr_fn,
    )

    mr_axiom_in_lst = mlList(Int, "in_lst")
    mr_axiom_index = Int("index")
    lm_fn_object = Fn((Int, Int), LM_NAME)
    lr_fn_object = Fn((Int, Int), LR_NAME)
    implies_expr = implies(
        and_objects(mr_axiom_index >= 0, mr_axiom_index < mr_axiom_in_lst.len()),
        call(
            "reduce",
            Int,
            call(
                "map", mlList[Int], mr_axiom_in_lst[: mr_axiom_index + 1], lm_fn_object
            ),
            lr_fn_object,
        )
        == call(
            LR_NAME,
            Int,
            call(
                "reduce",
                Int,
                call(
                    "map", mlList[Int], mr_axiom_in_lst[:mr_axiom_index], lm_fn_object
                ),
                lr_fn_object,
            ),
            call(LM_NAME, Int, mr_axiom_in_lst[mr_axiom_index]),
        ),
    ).src
    map_reduce_axiom = Axiom(implies_expr, mr_axiom_in_lst.src, mr_axiom_index.src)

    return [map_fn, reduce_fn, map_reduce_axiom, mapper, reducer]


def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    # reads = [data]
    ret_val = writes[0]
    data = reads[0]
    lm_fn_object = Fn((Int, Int), LM_NAME)
    lr_fn_object = Fn((Int, Int), LR_NAME)
    call_obj = call(
        "reduce", Int, call("map", mlList[Int], data, lm_fn_object), lr_fn_object
    )
    choices = choose(ret_val == call_obj, ret_val > call_obj)
    return choices


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Bool:
    # writes = [count, i]
    # reads = [data]
    lm_fn_object = Fn((Int, Int), LM_NAME)
    lr_fn_object = Fn((Int, Int), LR_NAME)
    count, i = writes
    data = reads[0]
    call_expr = call(
        "reduce", Int, call("map", mlList[Int], data[:i], lm_fn_object), lr_fn_object
    )

    count_inv_cond = choose(count == call_expr, count >= call_expr)
    in_lst_length = data.len()
    i_bound_in_lst_length_cond = choose(
        i >= in_lst_length,
        i <= in_lst_length,
        i > in_lst_length,
        i < in_lst_length,
        i == in_lst_length,
    )
    i_bound_int_lit = choose(Int(0), Int(1))
    i_bound_int_lit_cond = choose(
        i >= i_bound_int_lit,
        i <= i_bound_int_lit,
        i > i_bound_int_lit,
        i < i_bound_int_lit,
        i == i_bound_int_lit,
    )
    return choose(
        and_objects(i_bound_in_lst_length_cond, i_bound_int_lit_cond, count_inv_cond)
    )


if __name__ == "__main__":
    driver = Driver()
    driver.fns_synths = fns_synths()
    test = driver.analyze(
        llvm_filepath="tests/llvm/count.ll",
        loops_filepath="tests/llvm/count.loops",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammars=defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar=ps_grammar,
    )
    data = mlList(Int, "data")
    driver.add_var_object(data)

    test(data)

    driver.synthesize(filename="count")

    print("\n\ngenerated code:" + test.codegen(codegen))
