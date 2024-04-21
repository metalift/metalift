import os
import runpy
import sys
from os.path import basename, dirname, join
from pathlib import Path

from tenspiler.codegen.gemmini_codegen import gemmini_codegen
from tenspiler.codegen.utils import DataType
from tenspiler.tests.test_codegen import *


def find_all_drivers(driver_dirs):
    driver_files = []
    for root_dir in driver_dirs:
        for dirpath, dirnames, filenames in os.walk(root_dir):
            for filename in filenames:
                if filename.endswith("_driver.py"):
                    full_path = join(dirpath, filename)
                    driver_files.append(full_path)
    return driver_files


driver_dirs = ["tenspiler/c2taco/holing/driver/"]
driver_files = find_all_drivers(driver_dirs)

stored_path = "./tenspiler/benchmarking/gemmini/"
gemmini_not_comp = [
    "translate_array",
    "vcopy",
    "vmul",
    "vneg",
    "voffset",
    "vrecip",
    "diveq",
    "muleq",
    "negate",
    "subeq_sca",
    "array_inc",
    "cube_in_place",
    "fourth_in_place",
]
for script_path in driver_files:
    script_dir = dirname(script_path)
    script_basename = basename(script_path)
    script_name, _ = script_basename.rsplit(".", 1)

    if any(not_comp + "_driver" in script_basename for not_comp in gemmini_not_comp):
        continue

    if script_dir not in sys.path:
        sys.path.append(script_dir)

    result = runpy.run_module(script_name, run_name="__main__")

    if script_dir in sys.path:
        sys.path.remove(script_dir)

    driver = result.get("driver")

    # NOTE: All c2taco uses full integer
    gemmini_code = gemmini_codegen(
        driver.get_actual_ps_fn_decl(), driver.synthesized_fns, DataType.INT32
    )

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

    e2e_filename = join(stored_path, folder_name, f"{e2e_fn_name}.c")

    e2e_filepath = Path(e2e_filename)

    e2e_filepath.parent.mkdir(parents=True, exist_ok=True)

    with e2e_filepath.open("w") as file:
        file.write(gemmini_code_timing)


blend_func_names = [
    normal_blend_8,
    normal_blend_f,
    linear_burn_8,
    linear_dodge_8,
    screen_blend_8,
]
llama_func_names = [softmax_part3, rmsnorm_part1, matmul]

for func_name in blend_func_names + llama_func_names:
    ps_fn_decl, all_fn_decls, d_type = func_name()
    gemmini_code = gemmini_codegen(ps_fn_decl, all_fn_decls, d_type)
    e2e_fn_name = f"{func_name.__name__}_gemmini"
    path_obj = (
        Path(f"{stored_path}/blend/{e2e_fn_name}.c")
        if func_name in blend_func_names
        else Path(f"{stored_path}/llama/{e2e_fn_name}.c")
    )

    path_obj.parent.mkdir(parents=True, exist_ok=True)

    with path_obj.open("w") as file:
        file.write(gemmini_code)
