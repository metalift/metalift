import os
import runpy
import sys
from os.path import basename, dirname, join
from pathlib import Path

from tenspiler.codegen.gemmini_codegen import gemmini_codegen
from tenspiler.codegen.utils import DataType
from tenspiler.generated_code.benchmark_names import *


def find_all_drivers(driver_dirs):
    driver_files = {}
    for root_dir in driver_dirs:
        for dirpath, dirnames, filenames in os.walk(root_dir):
            for filename in filenames:
                if filename.endswith("_driver.py"):
                    benchmark_name = filename[:-10]  # remove the _driver.py at the end
                    full_path = join(dirpath, filename)
                    driver_files[benchmark_name] = full_path
    return driver_files


driver_dirs = [
    "tenspiler/c2taco/holing/driver/",
    "tenspiler/blend/holing/driver/",
    "tenspiler/llama/holing/driver/",
]
driver_files = find_all_drivers(driver_dirs)

stored_path = "./tenspiler/generated_code/gemmini/"


def generate_benchmark(benchmark_name):
    if benchmark_name not in all_test:
        print(
            f"Benchmark name {benchmark_name} is not in predefined benchmark name list!"
        )
        exit(1)

    data_type = None
    if benchmark_name in blend_test_name:
        if benchmark_name in gemmini_blend_func_names:
            data_type = DataType.UINT_8
        else:
            print(
                f"Benchmark name {benchmark_name} is not supported in Gemmini backend"
            )
            return
    elif benchmark_name in llama_test_name:
        if benchmark_name in gemmini_llama_func_names:
            data_type = DataType.FLOAT
        else:
            print(
                f"Benchmark name {benchmark_name} is not supported in Gemmini backend"
            )
            return
    elif benchmark_name not in gemmini_not_comp:
        data_type = DataType.INT32
    else:
        print(f"Benchmark name {benchmark_name} is not supported in Gemmini backend")
        return

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

    gemmini_code = gemmini_codegen(
        driver.get_actual_ps_fn_decl(), driver.synthesized_fns, data_type
    )

    print(f"Successfully generated code for {benchmark_name}")

    e2e_fn_name = f"{driver.get_actual_ps_fn_decl().name()[:-3]}_gemmini"

    # NOTE: The following if only needed for generating timing executables and need manual effort in connecting input.
    #     setup_code = """
    # // setup code
    # #include <stdint.h>
    # #include <stddef.h>
    # #include <assert.h>
    # #include <stdlib.h>
    # #include <stdio.h>
    # #ifndef BAREMETAL
    # #include <sys/mman.h>
    # #endif
    # #include "include/gemmini_testutils.h"

    # # define LEN

    # uint64_t start = 0;
    # uint64_t end = 0;

    # float random_float() {
    #     return (float)(rand()) / (float)(RAND_MAX);
    # }

    # uint8_t random_uint8() {
    #     return (uint8_t)(rand() % 256 - 128);
    # }

    # int32_t random_int() {
    #     return rand();
    # }

    # """

    gemmini_code_timing = gemmini_code
    #     gemmini_code_timing =  setup_code + gemmini_code + f"""
    # int main() {{
    # #ifndef BAREMETAL
    #     if (mlockall(MCL_CURRENT | MCL_FUTURE) != 0) {{
    #       perror("mlockall failed");
    #       exit(1);
    #     }}
    # #endif

    #     gemmini_flush(0);
    #     unsigned long long totalTime = 0;

    #     totalTime += end - start;

    #     printf("{e2e_fn_name}");
    #     printf("%llu\\n", totalTime);
    #     exit(0);
    # }}
    # """

    path_obj = Path(script_path)
    folder_name = path_obj.parent.name if path_obj.parent.name != "driver" else ""

    if benchmark_name in blend_test_name:
        folder_name = "blend"
    elif benchmark_name in llama_test_name:
        folder_name = "llama"

    e2e_filename = join(stored_path, folder_name, f"{e2e_fn_name}.c")

    e2e_filepath = Path(e2e_filename)

    e2e_filepath.parent.mkdir(parents=True, exist_ok=True)

    with e2e_filepath.open("w") as file:
        file.write(gemmini_code_timing)

    print(f"Stored the genereted code into {e2e_filename}")


def generate_benchmarks(benchmark_name):
    if benchmark_name == "ALL":
        for test in all_test:
            generate_benchmark(test)
    else:
        generate_benchmark(benchmark_name)
    print("Finished generation")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python generate_gemmini_benchmarks.py <benchmark name>")
        exit(1)
    generate_benchmarks(sys.argv[1])
