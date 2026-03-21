import time

from llm.synthesis import LLMModel, VerificationMethod, run_synthesis_for_cc
from metalift.ir import FnDecl, Int, fn_decl


def _fma_target_lang() -> list[FnDecl]:
    """
    fn_decl(name: str, return_type: Type, body: Expr, *args: Expr) -> FnDecl
    """
    x = Int("x")
    y = Int("y")
    z = Int("z")
    return [fn_decl("fma", Int, (x + y * z), x, y, z)]


if __name__ == "__main__":
    start_time = time.time()
    run_synthesis_for_cc(
        "tests/tutorial/fma_dsl/fma_dsl.cc",
        "fma_dsl",
        llm_model=LLMModel.BEDROCK,
        verification_method=VerificationMethod.SMT,
        dsl_fns=_fma_target_lang(),
        dsl_fn_name_to_axioms={},
    )
    print(f"Synthesis took {time.time() - start_time} seconds")
