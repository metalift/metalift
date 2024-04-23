import os
import runpy
import sys
from os.path import basename, dirname, join
from pathlib import Path

from tenspiler.codegen.gaudi_codegen import gaudi_codegen
from tenspiler.codegen.utils import DataType
from tenspiler.generated_code.benchmark_names import *


def find_all_drivers(driver_dirs):
    driver_files = {}
    for root_dir in driver_dirs:
        for dirpath, dirnames, filenames in os.walk(root_dir):
            for filename in filenames:
                if filename.endswith("_driver.py"):
                    benchmark_name = filename[:-10] # remove the _driver.py at the end
                    full_path = join(dirpath, filename)
                    driver_files[benchmark_name] = full_path
    return driver_files

driver_dirs = ["tenspiler/c2taco/holing/driver/", "tenspiler/blend/holing/driver/", "tenspiler/llama/holing/driver/"]
driver_files = find_all_drivers(driver_dirs)

stored_path = "./tenspiler/generated_code/gaudi/"

gaudi_not_comp = ['vcopy', 'mat1x3', 'gemv']
def generate_benchmark(benchmark_name):
    if benchmark_name not in all_test:
        print(f"Benchmark name {benchmark_name} is not in predefined benchmark name list!")
        exit(1)

    if benchmark_name in llama_test_name or benchmark_name in gaudi_not_comp:
        print(f"Benchmark name {benchmark_name} is not supported in Gaudi backend with TPC-C. See PyTorch version.")
        return

    data_type = None

    if benchmark_name in blend_test_name:
        data_type = DataType.UINT_8
    elif benchmark_name in llama_test_name:
        data_type = DataType.FLOAT
    else:
        data_type = DataType.INT32

    
    script_path = driver_files[benchmark_name]
    script_dir = dirname(script_path)
    script_basename = basename(script_path)
    script_name, _ = script_basename.rsplit(".", 1)

    if script_dir not in sys.path:
        sys.path.append(script_dir)

    result = runpy.run_module(script_name, run_name="__main__")

    print(f"Successfully executed driver file at {script_path}")

    if script_dir in sys.path:
        sys.path.remove(script_dir)

    driver = result.get("driver")

    gaudi_hpp_glue_code, gaudi_cpp_glue_code, gaudi_kernel_code = gaudi_codegen(
            driver.get_actual_ps_fn_decl(), driver.synthesized_fns, data_type
        )

    print(f"Successfully generated code for {benchmark_name}")

    path_obj = Path(script_path)
    folder_name = path_obj.parent.name if path_obj.parent.name != "driver" else ""

    if benchmark_name in blend_test_name:
        folder_name = "blend"
    elif benchmark_name in llama_test_name:
        folder_name = "llama"

    filepath = join(stored_path, folder_name)

    with open(filepath / f"{benchmark_name}_gaudi.hpp", "w") as f:
        f.write(gaudi_hpp_glue_code)
    with open(filepath / f"{benchmark_name}_gaudi.cpp", "w") as f:
        f.write(gaudi_cpp_glue_code)
    with open(filepath / f"{benchmark_name}_gaudi.c", "w") as f:
        f.write(gaudi_kernel_code)

    print(f"Stored the genereted code into {filepath}")


def generate_benchmarks(benchmark_name):
    if benchmark_name == "ALL":
        for test in all_test:
            generate_benchmark(test)
    else:
        generate_benchmark(benchmark_name)
    print("Finished generation")

if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python generate_gaudi_benchmarks.py <benchmark name>")
        exit(1)

    generate_benchmarks(sys.argv[1])