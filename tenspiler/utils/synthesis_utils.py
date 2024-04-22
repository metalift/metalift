import multiprocessing
import os
from pathlib import Path

from metalift.frontend.llvm import Driver
from metalift.synthesis_common import SynthesisFailed, VerificationFailed
from tenspiler.codegen.gaudi_codegen import gaudi_codegen
from tenspiler.codegen.numpy_codegen import numpy_codegen
from tenspiler.codegen.pytorch_codegen import pytorch_codegen
from tenspiler.codegen.tensorflow_codegen import tensorflow_codegen
from tenspiler.codegen.utils import DataType


def run_synthesize_with_bound(
    *,
    driver: Driver,
    data_type: DataType,
    benchmark_name: str,
    list_bound: int,
    max_rounds: int,
    has_relaxed: bool,
):
    try:
        print(f"Trying strict grammar with list bound {list_bound}...")
        # First use strict grammar
        basename = f"{benchmark_name}_strict_listbound{list_bound}_rounds{max_rounds}"
        driver.synthesize(
            filename=basename,
            list_bound=list_bound,
            relaxed_grammar=False,
            rounds_to_guess=max_rounds,
        )
    except SynthesisFailed as e:
        print(f"Strict grammar with list bound {list_bound} failed")
        if not has_relaxed:
            print("No relaxed grammar specified")
            raise e

        # Use relaxed grammar
        print("Trying relaxed grammar...")
        basename = f"{benchmark_name}_relaxed_listbound{list_bound}_rounds{max_rounds}"
        driver.synthesize(
            filename=basename,
            list_bound=list_bound,
            relaxed_grammar=True,
            rounds_to_guess=max_rounds,
        )

    ps_fn_decl = driver.get_actual_ps_fn_decl()

    curr_file_path = Path(__file__).resolve()
    tenspiler_dir = curr_file_path.parent.parent
    generated_code_dir = tenspiler_dir / "codegen" / "generated_code"
    generated_code_dir.mkdir(parents=True, exist_ok=True)

    # Write numpy code
    numpy_base_dir = generated_code_dir / "numpy"
    numpy_base_dir.mkdir(parents=True, exist_ok=True)
    np_code = numpy_codegen(ps_fn_decl, driver.synthesized_fns, data_type)
    with open(numpy_base_dir / f"{benchmark_name}.py", "w") as f:
        f.write(np_code)

    # Write tensorflow code
    tf_base_dir = generated_code_dir / "tensorflow"
    tf_base_dir.mkdir(parents=True, exist_ok=True)
    tf_code = tensorflow_codegen(ps_fn_decl, driver.synthesized_fns, data_type)
    with open(tf_base_dir / f"{benchmark_name}.py", "w") as f:
        f.write(tf_code)

    # Write pytorch code
    pt_base_dir = generated_code_dir / "pytorch"
    pt_base_dir.mkdir(parents=True, exist_ok=True)
    pt_code = pytorch_codegen(ps_fn_decl, driver.synthesized_fns, data_type)
    with open(generated_code_dir / "pytorch" / f"{benchmark_name}.py", "w") as f:
        f.write(pt_code)

    gaudi_base_dir = generated_code_dir / "gaudi" / benchmark_name
    gaudi_base_dir.mkdir(parents=True, exist_ok=True)
    gaudi_hpp_glue_code, gaudi_cpp_glue_code, gaudi_kernel_code = gaudi_codegen(
        ps_fn_decl, driver.synthesized_fns, data_type
    )

    with open(gaudi_base_dir / f"{benchmark_name}.hpp", "w") as f:
        f.write(gaudi_hpp_glue_code)
    with open(gaudi_base_dir / f"{benchmark_name}.cpp", "w") as f:
        f.write(gaudi_cpp_glue_code)
    with open(gaudi_base_dir / f"{benchmark_name}.c", "w") as f:
        f.write(gaudi_kernel_code)


def run_synthesize_algorithm(
    *,
    driver: Driver,
    data_type: DataType,
    benchmark_name: str,
    list_bound_start: int = 2,
    max_rounds: int = 10,
    has_relaxed: bool = False,
):
    list_bound = list_bound_start
    while True:
        try:
            run_synthesize_with_bound(
                driver=driver,
                data_type=data_type,
                benchmark_name=benchmark_name,
                list_bound=list_bound,
                max_rounds=max_rounds,
                has_relaxed=has_relaxed,
            )
            return
        except VerificationFailed:
            list_bound += 1
        except Exception as e:
            raise e


def run_synthesis_algorithm_with_timeout(
    *,
    driver: Driver,
    data_type: DataType,
    benchmark_name: str,
    max_rounds: int = 10,
    has_relaxed: bool = False,
    timeout: int = 1,  # Default timeout is 1 hour
):
    kwargs = {
        "driver": driver,
        "data_type": data_type,
        "benchmark_name": benchmark_name,
        "list_bound_start": os.getenv("LIST_BOUND_START", 2),
        "max_rounds": max_rounds,
        "has_relaxed": has_relaxed,
    }
    p = multiprocessing.Process(target=run_synthesize_algorithm, kwargs=kwargs)
    p.start()
    p.join(timeout)
    if p.is_alive():
        p.terminate()
        p.join()
        raise TimeoutError(f"Function execution timed out after {timeout} seconds")
