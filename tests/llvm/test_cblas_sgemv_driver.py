import time
from typing import List, Union

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import FnDecl, FnDeclRecursive, Int
from metalift.ir import List as mlList
from metalift.ir import Matrix, Object, call, choose, ite
from metalift.vc_util import and_objects
from tests.python.utils.utils import codegen


def cblas_sgemv(alpha: Int, a: Matrix[Int], x: Int, beta: Int, y: Int) -> mlList[Int]:
    return call("cblas_sgemv", mlList[Int], alpha, a, x, beta, y)


def sdot(x: mlList[Int], y: mlList[Int]) -> Int:
    return call("sdot", Int, x, y)


def sgemv(a: Matrix[Int], x: mlList[Int]) -> mlList[Int]:
    return call("sgemv", mlList[Int], a, x)


def target_lang() -> List[Union[FnDecl, FnDeclRecursive]]:
    x = mlList(Int, "x")
    y = mlList(Int, "y")
    sdot_cond = and_objects(x.len() > 0, y.len() > 0, x.len() == y.len())
    sdot_then = x[0] * y[0] + sdot(x[1:], y[1:])
    sdot_else = Int(0)
    sdot_decl = FnDeclRecursive(
        "sdot", Int, ite(sdot_cond, sdot_then, sdot_else).src, x.src, y.src
    )

    a = mlList(mlList[Int], "a")
    x = mlList(Int, "x")
    sgemv_cond = x.len() == a[0].len()
    sgemv_then = sgemv(a[1:], x).prepend(sdot(a[0], x))
    sgemv_else = mlList.empty(Int)
    sgemv_decl = FnDeclRecursive(
        "sgemv", mlList[Int], ite(sgemv_cond, sgemv_then, sgemv_else).src, a.src, x.src
    )

    alpha = Int("alpha")
    a = mlList(mlList[Int], "a")
    x = mlList(Int, "x")
    beta = Int("beta")
    y = mlList(Int, "y")
    cblas_sgemv_cond = and_objects(
        a.len() > 0, a[0].len() > 0, a[0].len() == x.len(), a.len() == y.len()
    )
    cblas_sgemv_then = cblas_sgemv(alpha, a[1:], x, beta, y[1:]).prepend(
        alpha * sdot(a[0], x) + beta * y[0]
    )
    cblas_sgemv_else = mlList.empty(Int)
    cblas_sgemv_decl = FnDeclRecursive(
        "cblas_sgemv",
        mlList[Int],
        ite(cblas_sgemv_cond, cblas_sgemv_then, cblas_sgemv_else).src,
        alpha.src,
        a.src,
        x.src,
        beta.src,
        y.src,
    )
    return [sdot_decl, sgemv_decl, cblas_sgemv_decl]


def inv0_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Object:
    z, i, j, _, res = writes
    alpha, a, x, beta, y = reads
    lower_bound = choose(Int(0), Int(1))
    i_lower_cond = choose(
        i >= lower_bound,
        i <= lower_bound,
    )
    i_upper_cond = choose(
        i <= a.len(),
        i >= a.len(),
    )
    index = choose(i, j)
    result = and_objects(
        i_lower_cond,
        i_upper_cond,
        z == cblas_sgemv(alpha, a[:index], x, beta, y[:index]),
    )
    return result


# TODO(jie): only keep i and agg.result from in_scope
def inv1_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Object:
    # Inner loop
    j, res = writes
    alpha, a, x, beta, y = reads
    in_scope_mapping = {obj.var_name(): obj for obj in in_scope}
    i = in_scope_mapping["i"]
    z = in_scope_mapping["agg.result"]
    lower_bound = choose(Int(0), Int(1))
    j_lower_cond = choose(
        j >= lower_bound,
        j <= lower_bound,
    )
    j_upper_cond = choose(
        j <= x.len(),
        j >= x.len(),
    )
    i_lower_cond = choose(
        i >= lower_bound,
        i <= lower_bound,
    )
    i_upper_cond = choose(
        i <= a.len(),
        i < a.len(),
    )

    sdot_list_take_index = choose(i, j)
    result = and_objects(
        j_lower_cond,
        j_upper_cond,
        i_lower_cond,
        i_upper_cond,
        # res == sdot(a[i][:j], x[:j]),
        res
        == sdot(
            a[sdot_list_take_index][:sdot_list_take_index], x[:sdot_list_take_index]
        ),
        z
        == cblas_sgemv(
            alpha, a[:sdot_list_take_index], x, beta, y[:sdot_list_take_index]
        ),
    )
    return result


def ps_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object]
) -> Object:
    ret_val = writes[0]
    alpha, a, x, beta, y = reads
    vec = choose(x, y)
    return ret_val == cblas_sgemv(alpha, a, x, beta, y)


if __name__ == "__main__":
    driver = Driver()
    test_cblas_sgemv = driver.analyze(
        llvm_filepath="tests/llvm/test_cblas_sgemv.ll",
        loops_filepath="tests/llvm/test_cblas_sgemv.loops",
        fn_name="test_cblas_sgemv",
        target_lang_fn=target_lang,
        inv_grammars={
            "test_cblas_sgemv_inv0": InvGrammar(inv0_grammar, []),
            "test_cblas_sgemv_inv1": InvGrammar(inv1_grammar, ["i", "agg.result"]),
        },
        ps_grammar=ps_grammar,
    )

    alpha = Int("alpha")
    a = mlList(mlList[Int], "a")
    x = mlList(Int, "x")
    beta = Int("beta")
    y = mlList(Int, "y")
    driver.add_var_objects([alpha, a, x, beta, y])
    driver.add_precondition(x.len() == a[0].len())
    driver.add_precondition(y.len() == a.len())
    driver.add_precondition(a.len() > 1)

    test_cblas_sgemv(alpha, a, x, beta, y)

    start_time = time.time()
    driver.synthesize(filename="test_cblas_sgemv", no_verify=True)
    end_time = time.time()

    print(f"Synthesis took {end_time - start_time} seconds")

    print("\n\ngenerated code:" + test_cblas_sgemv.codegen(codegen))
