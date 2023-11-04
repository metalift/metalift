from typing import List, Union

from metalift.frontend.python import Driver
from metalift.ir import (Axiom, BoolObject, FnDecl, FnDeclObject,
                         FnDeclRecursive, IntObject, ListObject, NewObject,
                         Synth, call, call_value, choose, fn_decl,
                         fn_decl_recursive, implies, ite)
from metalift.vc_util import and_objects
from tests.python.utils.utils import codegen

# We need to define some global variables as they need to persist across function calls
LM_NAME = "lm"
LR_NAME = "lr"
val = IntObject("val")
val2 = IntObject("val2")

def fns_synths() -> List[Synth]:
    lm_synth = Synth(
        LM_NAME,
        choose(IntObject(0), IntObject(1), IntObject(2), IntObject(3)).src,
        val.src
    )
    v = choose(val, val2)
    lr_synth = Synth(
        LR_NAME,
        choose(v + v, v - v, v * v).src,
        val.src,
        val2.src
    )
    return [lm_synth, lr_synth]

def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    in_lst = ListObject(IntObject, "in_lst")
    lm_fn = FnDeclObject((IntObject, IntObject), "f")
    lr_fn = FnDeclObject((IntObject, IntObject, IntObject), "f")

    mapper = fn_decl(LM_NAME, IntObject, None, val)
    reducer = fn_decl(LR_NAME, IntObject, None, val, val2)

    map_fn = fn_decl_recursive(
        "map",
        ListObject[IntObject],
        ite(
            in_lst.len() == 0,
            ListObject.empty(IntObject),
            call("map", ListObject[IntObject], in_lst[1:], lm_fn).prepend(call_value(lm_fn, in_lst[0]))
        ),
        in_lst,
        lm_fn,
    )

    reduce_fn = fn_decl_recursive(
        "reduce",
        IntObject,
        ite(
            in_lst.len() == 0,
            IntObject(0),
            call_value(lr_fn, in_lst[0], call("reduce", IntObject, in_lst[1:], lr_fn))
        ),
        in_lst,
        lr_fn,
    )

    mr_axiom_in_lst = ListObject(IntObject, "in_lst")
    mr_axiom_index = IntObject("index")
    lm_fn_object = FnDeclObject((IntObject, IntObject), LM_NAME)
    lr_fn_object = FnDeclObject((IntObject, IntObject), LR_NAME)
    implies_expr = implies(
        and_objects(mr_axiom_index >= 0, mr_axiom_index < mr_axiom_in_lst.len()),
        call(
            "reduce",
            IntObject,
            call(
                "map",
                ListObject[IntObject],
                mr_axiom_in_lst[mr_axiom_index + 1],
                lm_fn_object
            ),
            lr_fn_object
        ) == call(
            LR_NAME,
            IntObject,
            call(
                "reduce",
                IntObject,
                call(
                    "map",
                    ListObject[IntObject],
                    mr_axiom_in_lst[:mr_axiom_index],
                    lm_fn_object
                ),
                lr_fn_object
            ),
            call(
                LM_NAME,
                IntObject,
                mr_axiom_in_lst[mr_axiom_index]
            ),
        )
    ).src
    map_reduce_axiom = Axiom(implies_expr, mr_axiom_in_lst.src, mr_axiom_index.src)

    return [map_fn, reduce_fn, map_reduce_axiom, mapper, reducer]

def ps_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> BoolObject:
    # reads = [in_lst]
    ret_val = writes[0]
    in_lst = reads[0]
    lm_fn_object = FnDeclObject((IntObject, IntObject), LM_NAME)
    lr_fn_object = FnDeclObject((IntObject, IntObject), LR_NAME)
    call_obj = call(
        "reduce",
        IntObject,
        call("map", ListObject[IntObject], in_lst, lm_fn_object),
        lr_fn_object
    )
    choices = choose(
        ret_val == call_obj,
        ret_val > call_obj
    )
    return choices

def inv_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> BoolObject:
    # writes = [count, i]
    # reads = [count, i, in_lst]
    lm_fn_object = FnDeclObject((IntObject, IntObject), LM_NAME)
    lr_fn_object = FnDeclObject((IntObject, IntObject), LR_NAME)
    count, i = writes
    in_lst = reads[2]
    call_expr = call(
        "reduce",
        IntObject,
        call(
            "map",
            ListObject[IntObject],
            in_lst[:i],
            lm_fn_object
        ),
        lr_fn_object
    )

    count_inv_cond = choose(
        count == call_expr,
        count >= call_expr
    )
    in_lst_length = in_lst.len()
    i_bound_in_lst_length_cond = choose(
        i >= in_lst_length,
        i <= in_lst_length,
        i > in_lst_length,
        i < in_lst_length,
        i == in_lst_length,
    )
    i_bound_int_lit = choose(IntObject(0), IntObject(1))
    i_bound_int_lit_cond = choose(
        i >= i_bound_int_lit,
        i <= i_bound_int_lit,
        i > i_bound_int_lit,
        i < i_bound_int_lit,
        i == i_bound_int_lit,
    )
    return choose(and_objects(i_bound_in_lst_length_cond, i_bound_int_lit_cond, count_inv_cond))

if __name__ == "__main__":
    filename = "tests/python/count.py"

    driver = Driver()
    driver.fns_synths = fns_synths()
    test = driver.analyze(
        filename,
        "test",
        target_lang,
        inv_grammar,
        ps_grammar
    )

    in_lst = ListObject(IntObject, "in_lst")

    test(in_lst)

    driver.synthesize()

    print("\n\ngenerated code:" + test.codegen(codegen))
