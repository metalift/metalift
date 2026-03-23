import time
from typing import cast

from llm.parser import get_dsl_func_defs
from llm.synthesis import LLMModel, VerificationMethod, run_synthesis_for_cc
from metalift.frontend.llvm import Driver
from metalift.ir import (
    Eq,
    Expr,
    FnDecl,
    FnDeclRecursive,
    Int,
    List,
    Object,
    Var,
    call,
    fn_decl,
    fn_decl_recursive,
    ite,
)
from tenspiler.axioms import (
    list_take_axiom,
    list_take_length_axiom,
    reduce_sum_vec_elemwise_mul_axiom,
    vec_elemwise_mul_axiom,
    vec_elemwise_mul_list_append_axiom,
    vec_scalar_mul_axiom,
    vec_scalar_mul_list_append_axiom,
    vec_scalar_mul_list_length_axiom,
)
from tenspiler.tenspiler_common import reduce_sum, vec_elemwise_mul, vec_scalar_mul
from tests.tutorial.rmsnorm.rmsnorm_codegen import nki_codegen, nki_template

# ── reduce_sum ──────────────────────────────────────────────────────
REDUCE_SUM = "reduce_sum"


def call_reduce_sum(x: List[Int]) -> Int:
    return call(REDUCE_SUM, Int, x)


def reduce_sum_body(x: List[Int]) -> Int:
    vec_size = x.len()
    cur = x[0]
    recursed = call_reduce_sum(x[1:])
    general_answer = cur + recursed
    return ite(vec_size < 1, Int(0), general_answer)


x = List(Int, "x")
reduce_sum = fn_decl_recursive(REDUCE_SUM, Int, reduce_sum_body(x), x)

# ── vec_elemwise_mul ────────────────────────────────────────────────
VEC_ELEMWISE_MUL = "vec_elemwise_mul"


def call_vec_elemwise_mul(x: List[Int], y: List[Int]) -> List[Int]:
    return call(VEC_ELEMWISE_MUL, List[Int], x, y)


def vec_elemwise_mul_body(x: List[Int], y: List[Int]) -> List[Int]:
    vec_size = x.len()
    cur = x[0] * y[0]
    recursed = call_vec_elemwise_mul(x[1:], y[1:])
    general_answer = recursed.prepend(cur)
    return ite(vec_size < 1, List.empty(Int), general_answer)


x = List(Int, "x")
y = List(Int, "y")
vec_elemwise_mul = fn_decl_recursive(
    VEC_ELEMWISE_MUL, List[Int], vec_elemwise_mul_body(x, y), x, y
)

# ── vec_scalar_mul ──────────────────────────────────────────────────
VEC_SCALAR_MUL = "vec_scalar_mul"


def call_vec_scalar_mul(a: Int, x: List[Int]) -> List[Int]:
    return call(VEC_SCALAR_MUL, List[Int], a, x)


def vec_scalar_mul_body(a: Int, x: List[Int]) -> List[Int]:
    vec_size = x.len()
    cur = a * x[0]
    recursed = call_vec_scalar_mul(a, x[1:])
    general_answer = recursed.prepend(cur)
    return ite(vec_size < 1, List.empty(Int), general_answer)


a = Int("a")
x = List(Int, "x")
vec_scalar_mul = fn_decl_recursive(
    VEC_SCALAR_MUL, List[Int], vec_scalar_mul_body(a, x), a, x
)

# ── integer_sqrt ────────────────────────────────────────────────────
INTEGER_SQRT = "integer_sqrt"


def call_integer_sqrt(x: Int) -> Int:
    return call(INTEGER_SQRT, Int, x)


def integer_sqrt_body(x: Int) -> Int:
    return call_integer_sqrt(x)


integer_sqrt = fn_decl(INTEGER_SQRT, Int, Int("x"), Int("x"))

# ── reduce_sum ──────────────────────────────────────────────────────
REDUCE_SUM = "reduce_sum"


def call_reduce_sum(x: List[Int]) -> Int:
    return call(REDUCE_SUM, Int, x)


def reduce_sum_body(x: List[Int]) -> Int:
    vec_size = x.len()
    cur = x[0]
    recursed = call_reduce_sum(x[1:])
    general_answer = cur + recursed
    return ite(vec_size < 1, Int(0), general_answer)


x = List(Int, "x")
reduce_sum = fn_decl_recursive(REDUCE_SUM, Int, reduce_sum_body(x), x)


# ── preconditions ────────────────────────────────────────────────────
def _rmsnorm_part1_preconditions(driver: Driver, input_vars: dict[str, Object]) -> None:
    input_var = input_vars["input"]
    driver.add_precondition(input_var.len() >= 1)


def _rmsnorm_part2_preconditions(driver: Driver, input_vars: dict[str, Object]) -> None:
    input_var = input_vars["input"]
    weight_var = input_vars["weight"]
    ss_var = input_vars["ss"]
    driver.add_precondition(input_var.len() >= 1)
    driver.add_precondition(input_var.len() == weight_var.len())
    driver.add_precondition(ss_var > Int(0))


def _extract_ps_body(
    synthesized_fn_decls: list[FnDecl | FnDeclRecursive], ps_name: str
) -> Expr:
    ps_decl = next(
        fn_decl for fn_decl in synthesized_fn_decls if fn_decl.name() == ps_name
    )
    ps_body = ps_decl.body()
    if not isinstance(ps_body, Eq):
        raise ValueError(f"Expected {ps_name} body to be Eq, got {type(ps_body)}")
    return cast(Eq, ps_body).e2()


def _substitute_var(expr: Expr, var_name: str, replacement: Expr) -> Expr:
    if isinstance(expr, Var) and expr.name() == var_name:
        return replacement
    return expr.map_args(
        lambda x: _substitute_var(x, var_name, replacement)
        if isinstance(x, Expr)
        else x
    )


def _compose_rmsnorm_fn(
    *,
    part1_ps_body: Expr,
    part2_ps_body: Expr,
) -> FnDeclRecursive:
    input_var = List(Int, "input")
    weight_var = List(Int, "weight")
    # Part2 expression refers to `ss`; replace it with part1 synthesized expression.
    combined_body = _substitute_var(part2_ps_body, "ss", part1_ps_body)
    return fn_decl_recursive(
        "rmsnorm_synthesized",
        List[Int],
        combined_body,
        input_var,
        weight_var,
    )


if __name__ == "__main__":
    start_time = time.time()

    print("Synthesizing rmsnorm_part1...")
    part1_decls = run_synthesis_for_cc(
        cc_path="tests/tutorial/rmsnorm/rmsnorm_part1.cc",
        fn_name="rmsnorm_part1",
        precondition_fn=_rmsnorm_part1_preconditions,
        llm_model=LLMModel.BEDROCK,
        dsl_fns=[reduce_sum, vec_elemwise_mul],
        verification_method=VerificationMethod.SMT,
        additional_axioms=[reduce_sum_vec_elemwise_mul_axiom],
    )
    part1_body = _extract_ps_body(part1_decls, "rmsnorm_part1_ps")
    get_dsl_func_defs.cache_clear()

    print("Synthesizing rmsnorm_part2...")
    part2_decls = run_synthesis_for_cc(
        cc_path="tests/tutorial/rmsnorm/rmsnorm_part2.cc",
        fn_name="rmsnorm_part2",
        precondition_fn=_rmsnorm_part2_preconditions,
        llm_model=LLMModel.BEDROCK,
        dsl_fns=[vec_elemwise_mul, vec_scalar_mul, integer_sqrt],
        verification_method=VerificationMethod.SMT,
        additional_axioms=[
            list_take_axiom,
            vec_elemwise_mul_axiom,
            vec_scalar_mul_axiom,
            vec_elemwise_mul_list_append_axiom,
            vec_scalar_mul_list_append_axiom,
            list_take_length_axiom,
            vec_scalar_mul_list_length_axiom,
        ],
    )
    part2_body = _extract_ps_body(part2_decls, "rmsnorm_part2_ps")

    combined_fn = _compose_rmsnorm_fn(
        part1_ps_body=part1_body,
        part2_ps_body=part2_body,
    )

    print("Combined synthesized function:")
    print(combined_fn.to_python())
    output_path = "synthesisLogs/rmsnorm.py"
    with open(output_path, "w") as f:
        f.write(combined_fn.to_python() + "\n")
    print(f"Wrote function to {output_path}")

    end_time = time.time()
    print(f"Total synthesis took {end_time - start_time} seconds")

    instruction_list: list[str] = []
    vec_shape_map: dict[str, tuple[str, str]] = {}
    output_buffer_name = nki_codegen(
        combined_fn.body(), instruction_list, vec_shape_map
    )
    template_code = nki_template(instruction_list, output_buffer_name, vec_shape_map)
    with open("synthesisLogs/rmsnorm_nki.py", "w") as f:
        f.write(template_code)
    print(f"Wrote function to {output_path}")
