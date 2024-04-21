from typing import List

from metalift.frontend.llvm import Driver
from metalift.ir import Object
from metalift.synthesis_common import SynthesisFailed, VerificationFailed
from tenspiler.codegen.numpy_codegen import numpy_codegen
from tenspiler.codegen.pytorch_codegen import pytorch_codegen
from tenspiler.codegen.tensorflow_codegen import tensorflow_codegen
from tenspiler.codegen.utils import Backend, DataType


def synthesize_with_bound(
    *,
    driver: Driver,
    backend: Backend,
    data_type: DataType,
    benchmark_name: str,
    benchmark_args: List[Object],
    list_bound: int,
    max_rounds: int,
):
    try:
        # First use strict grammar
        basename = f"{benchmark_name}_strict_listbound{list_bound}_rounds{max_rounds}"
        driver.synthesize(
            fn_name=benchmark_name,
            fn_args=benchmark_args,
            filename=basename,
            list_bound=list_bound,
            relaxed_grammar=False,
            rounds_to_guess=max_rounds,
        )
    except SynthesisFailed:
        # If strict grammar fails, use relaxed grammar
        basename = f"{benchmark_name}_relaxed_listbound{list_bound}_rounds{max_rounds}"
        driver.synthesize(
            fn_name=benchmark_name,
            fn_args=benchmark_args,
            filename=basename,
            list_bound=list_bound,
            relaxed_grammar=True,
            rounds_to_guess=max_rounds,
        )

    ps_fn_decl = driver.get_actual_ps_fn_decl()

    if backend == Backend.NUMPY:
        np_code = numpy_codegen(ps_fn_decl, driver.synthesized_fns, data_type)
        print(np_code)
    elif backend == Backend.TENSORFLOW:
        tf_code = tensorflow_codegen(ps_fn_decl, driver.synthesized_fns, data_type)
        print(tf_code)
    elif backend == Backend.PYTORCH:
        pt_code = pytorch_codegen(ps_fn_decl, driver.synthesized_fns, data_type)
        print(pt_code)


def synthesize_algorithm(
    *,
    driver: Driver,
    backend: Backend,
    data_type: DataType,
    benchmark_name: str,
    benchmark_args: List[Object],
    list_bound_start: int = 2,
    max_rounds: int = 10,
):
    list_bound = list_bound_start
    while True:
        try:
            synthesize_with_bound(
                driver=driver,
                backend=backend,
                data_type=data_type,
                benchmark_name=benchmark_name,
                benchmark_args=benchmark_args,
                list_bound=list_bound,
                max_rounds=max_rounds,
            )
        except VerificationFailed:
            list_bound += 1
        except Exception as e:
            raise e
