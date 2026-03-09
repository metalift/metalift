from collections import defaultdict
from typing import List

from metalift.frontend.llvm import Driver, InvGrammar
from metalift.ir import Bool, FnDecl, Int, Object, call, choose, fn_decl
from tests.python.utils.utils import codegen


def target_lang() -> List[FnDecl]:
    x = Int("x")
    y = Int("y")
    z = Int("z")
    fma = fn_decl("fma", Int, (x + y * z), x, y, z)
    return [fma]


def inv_grammar(
    writes: List[Object], reads: List[Object], in_scope: List[Object], relaxed: bool
) -> Bool:
    raise Exception("no loop in the source")


if __name__ == "__main__":
    driver = Driver()
    test = driver.analyze(
        llvm_filepath="tests/llvm/fma_dsl.ll",
        loops_filepath="tests/llvm/fma_dsl.loops",
        fn_name="test",
        target_lang_fn=target_lang,
        inv_grammars=defaultdict(lambda: InvGrammar(inv_grammar, [])),
        ps_grammar=None,
    )

    base = Int("base")
    arg1 = Int("arg1")
    base2 = Int("base2")
    arg2 = Int("arg2")
    driver.add_var_objects([base, arg1, base2, arg2])

    test(base, arg1, base2, arg2)

    input_code = Path("tests/llvm/fma_dsl.c").read_text()
    start_time = time.time()
    run_llm_synthesis_algorithm(
        driver=driver,
        source_code=input_code,
        benchmark_name="fma_dsl",
        llm_model=LLMModel.GPT,
        dsl_fns=target_lang,
        verification_method=VerificationMethod.ROSETTE
    )
    end_time = time.time()
    print(f"Synthesis took {end_time - start_time} seconds")
