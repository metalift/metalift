from typing import List, Union
from metalift.frontend.llvm import Driver
from metalift.ir import FnDecl, FnDeclRecursive, IntObject, ListObject, NewObject, call, choose, ite
from metalift.vc_util import and_objects
from tests.python.utils.utils import codegen

def cblas_sgemv(
    alpha: IntObject,
    a: ListObject[ListObject[IntObject]],
    x: IntObject,
    beta: IntObject,
    y: IntObject
) -> ListObject[IntObject]:
    return call("cblas_sgemv", ListObject[IntObject], alpha, a, x, beta, y)

def sdot(x: ListObject[IntObject], y: ListObject[IntObject]) -> IntObject:
    return call("sdot", IntObject, x, y)

def sgemv(a: ListObject[ListObject[IntObject]], x: ListObject[IntObject]) -> ListObject[IntObject]:
    return call("sgemv", ListObject[IntObject], a, x)

def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    x = ListObject(IntObject, "x")
    y = ListObject(IntObject, "y")
    sdot_cond = and_objects(x.len() > 0, y.len() > 0, x.len() == y.len())
    sdot_then = x[0] * y[0] + sdot(x[1:], y[1:])
    sdot_else = IntObject(0)
    sdot_decl = FnDeclRecursive(
        "sdot",
        IntObject,
        ite(sdot_cond, sdot_then, sdot_else).src,
        x.src,
        y.src
    )

    a = ListObject(ListObject[IntObject], "a")
    x = ListObject(IntObject, "x")
    sgemv_cond = x.len() == a[0].len()
    sgemv_then = sgemv(a[1:], x).prepend(sdot(a[0], x))
    sgemv_else = ListObject.empty(IntObject)
    sgemv_decl = FnDeclRecursive(
        "sgemv",
        ListObject[IntObject],
        ite(sgemv_cond, sgemv_then, sgemv_else).src,
        a.src,
        x.src
    )

    alpha = IntObject("alpha")
    a = ListObject(ListObject[IntObject], "a")
    x = ListObject(IntObject, "x")
    beta = IntObject("beta")
    y = ListObject(IntObject, "y")
    cblas_sgemv_cond = and_objects(
        a.len() > 0,
        a[0].len() > 0,
        a[0].len() == x.len(),
        a.len() == y.len()
    )
    cblas_sgemv_then = cblas_sgemv(alpha, a[1:], x, beta, y[1:]).prepend(alpha * sdot(a[0], x) + beta * y[0])
    cblas_sgemv_else = ListObject.empty(IntObject)
    cblas_sgemv_decl = FnDeclRecursive(
        "cblas_sgemv",
        ListObject[IntObject],
        ite(cblas_sgemv_cond, cblas_sgemv_then, cblas_sgemv_else).src,
        alpha.src,
        a.src,
        x.src,
        beta.src,
        y.src,
    )
    return [sdot_decl, sgemv_decl, cblas_sgemv_decl]

def inv0_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> NewObject:
    # Outer loop
    z, res, j, _, i = writes
    alpha, a, x, beta, y = reads
    i_lower_cond = choose(
        i >= 0,
        # i > 0
    )
    i_upper_cond = choose(
        i <= a.len(),
        # i < a.len()
    )
    result = and_objects(
        i_lower_cond,
        i_upper_cond,
        z == cblas_sgemv(alpha, a[:i], x, beta, y[:i])
    )
    return result

# TODO(jie): only keep i and agg.result from in_scope
def inv1_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> NewObject:
    # Inner loop
    res, j = writes
    alpha, a, x, beta, y = reads
    in_scope_mapping = {
        obj.var_name(): obj
        for obj in in_scope
    }
    i = in_scope_mapping["i"]
    z = in_scope_mapping["agg.result"]
    j_lower_cond = choose(
        j >= 0,
        # j > 0
    )
    j_upper_cond = choose(
        j <= x.len(),
        # j < x.len()
    )
    i_lower_cond = choose(
        i >= 0,
        # i > 0
    )
    i_upper_cond = choose(
        # i <= a.len(),
        i < a.len()
    )

    result = and_objects(
        j_lower_cond,
        j_upper_cond,
        i_lower_cond,
        i_upper_cond,
        res == sdot(a[i][:j], x[:j]),
        z == cblas_sgemv(alpha, a[:i], x, beta, y[:i])
    )
    return result

def ps_grammar(writes: List[NewObject], reads: List[NewObject], in_scope: List[NewObject]) -> NewObject:
    ret_val = writes[0]
    alpha, a, x, beta, y = reads
    return ret_val == cblas_sgemv(alpha, a, x, beta, y)

if __name__ == "__main__":
    driver = Driver()
    test_cblas_sgemv = driver.analyze(
        llvm_filepath="tests/llvm/test_cblas_sgemv.ll",
        loops_filepath="tests/llvm/test_cblas_sgemv.loops",
        fn_name="test_cblas_sgemv",
        target_lang_fn=target_lang,
        inv_grammars={
            "test_cblas_sgemv_inv0": inv0_grammar,
            "test_cblas_sgemv_inv1": inv1_grammar
        },
        ps_grammar=ps_grammar
    )

    alpha = IntObject("alpha")
    a = ListObject(ListObject[IntObject], "a")
    x = ListObject(IntObject, "x")
    beta = IntObject("beta")
    y = ListObject(IntObject, "y")
    driver.add_var_objects([alpha, a, x, beta, y])
    driver.add_precondition(x.len() == a[0].len())
    driver.add_precondition(y.len() == a.len())
    driver.add_precondition(a.len() > 1)

    test_cblas_sgemv(alpha, a, x, beta, y)

    driver.synthesize(noVerify=True)

    print("\n\ngenerated code:" + test_cblas_sgemv.codegen(codegen))
