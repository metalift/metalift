import time

from llm.synthesis import LLMModel, VerificationMethod, run_synthesis_for_cc
from metalift.ir import FnDecl, Int, fn_decl, ite


def _target_lang() -> list[FnDecl]:
    # DSL extension
    x = Int("x")
    y = Int("y")
    z = Int("z")
    fma = fn_decl("fma", Int, x + y * z, x, y, z)
    relu = fn_decl("relu", Int, ite(x > Int(0), x, Int(0)), x)
    fma_relu = fn_decl(
        "fma_relu",
        Int,
        ite(x + y * z > Int(0), x + y * z, Int(0)),
        x,
        y,
        z,
    )
    return [fma, relu, fma_relu]


if __name__ == "__main__":
    start_time = time.time()
    run_synthesis_for_cc(
        "tests/tutorial/conv_activation.cc",
        "conv_activation",
        llm_model=LLMModel.GPT,
        verification_method=VerificationMethod.SMT,
        dsl_fns=_target_lang(),
        dsl_fn_name_to_axioms={},
    )
    print(f"Synthesis took {time.time() - start_time} seconds")

