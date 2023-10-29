from typing import List, Union
from metalift.frontend.llvm import Driver
from metalift.ir import FnDecl, FnDeclRecursive, IntObject, ListObject, NewObject, call, ite
from metalift.vc_util import and_objects
from tests.python.utils.utils import codegen

def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    x = ListObject(IntObject, "x")
    y = ListObject(IntObject, "y")
    sdot_cond = and_objects(x.len() > 0, y.len() > 0, x.len() == y.len())
    sdot_then = x[0] * y[0] + call("sdot", x[1:], y[1:])
    sdot_else = IntObject(0)
    sdot = FnDeclRecursive(
        "sdot",
        IntObject,
        ite(sdot_cond, sdot_then, sdot_else).src,
        x.src,
        y.src
    )

    a = ListObject(ListObject[IntObject], "a")
    x = ListObject(IntObject, "x")
    sgemv_cond = x.len() == a[0].len()
    sgemv_then = call("sgemv", a[1:], x).prepend(call("sdot", a[0], x))
    sgemv_else = ListObject.empty(IntObject)
    sgemv = FnDeclRecursive(
        "sgemv",
        ListObject[IntObject],
        ite(sgemv_cond, sgemv_then, sgemv_else).src,
        x.src,
        y.src
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
    cblas_sgemv_else = call("cblas_sgemv", alpha, a[1:], x, beta, y[1:]).prepend(alpha * call("sdot", a[0], x) + beta * y[0])
    cblas_sgemv_then = ListObject.empty(IntObject)
    cblas_sgemv = FnDeclRecursive(
        "cblas_sgemv",
        ListObject[IntObject],
        ite(cblas_sgemv_cond, cblas_sgemv_then, cblas_sgemv_else).src,
        alpha.src,
        a.src,
        x.src,
        beta.src,
        y.src,
    )
    return [cblas_sgemv]

def inv0_grammar(writes: List[NewObject], reads: List[NewObject]) -> NewObject:
    res, j, z, i = writes
    alpha, a, x, beta, y = reads

    and_objects(
        i >= 0,
        i <= a.len(),
        z == call("cblas_sgemv", alpha, a[:i], x, beta, y[:i])
    )

def inv1_grammar(writes: List[NewObject], reads: List[NewObject]) -> NewObject:
    res, j, z, i = writes
    alpha, a, x, beta, y = reads
    return and_objects(
        j >= 0,
        j <= x.len(),
        i >= 0,
        i < a.len(),
        res == call("sdot", a[i][:j], x[:j]),
        z == call("cblas_sgemv", alpha, a[:i], x, beta, y[:i])
    )

def ps_grammar(writes: List[NewObject], reads: List[NewObject]) -> NewObject:
    ret_val = writes[0]
    alpha, a, x, beta, y = reads
    return ret_val == call("cblas_sgemv", alpha, a, x, beta, y)

if __name__ == "__main__":
    driver = Driver()
    test_cblas_sgemv = driver.analyze(
        llvm_filepath="tests/llvm/test_cblas_sgemv.ll",
        loops_filepath="tests/llvm/test_cblas_sgemv.loops",
        fn_name="test_cblas_sgemv",
        target_lang_fn=target_lang,
        inv_grammar=inv1_grammar,
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

    driver.synthesize()

    print("\n\ngenerated code:" + test_cblas_sgemv.codegen(codegen))
