import os
import shutil
import subprocess
import sys

import numpy as np

from tenspiler.benchmarking.gemmini_exec_makefile_helper import *
from tenspiler.benchmarking.utils import *

gemmini_dir = os.path.join(parent_path, "gemmini")

gemmini_parent_path = ""
gemmini_rocc_tests_dir = os.path.join(gemmini_parent_path, "gemmini-rocc-tests")
gemmini_simulator_dir = os.path.join(gemmini_parent_path, "gemmini")

gemmini_storage_dir = os.path.join(gemmini_rocc_tests_dir, "bareMetalC")
gemmini_makefile_path = os.path.join(gemmini_storage_dir, "Makefile")
gemmini_build_path = os.path.join(gemmini_rocc_tests_dir, "build.sh")

gemmini_run_script_path = os.path.join(gemmini_simulator_dir, "scripts", "run-vcs.sh")

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
gemmini_blend_func_names = [
    "normal_blend_8",
    "normal_blend_f",
    "linear_burn_8",
    "linear_dodge_8",
    "screen_blend_8",
]
gemmini_llama_func_names = ["softmax_part3", "rmsnorm_part1", "matmul"]

gemmini_runtime_conversion = {"matmul": 240, "rmsnorm_part1": 241, "softmax_part3": 240}


def setup_gemmini(src_filepath, filename):
    print("Copying file to gemmini-rocc-tests/bareMetalC ")
    shutil.copy(src_filepath, gemmini_storage_dir)

    print("Rewriting gemmini-rocc-tests/bareMetalC/makefile to include benchmark ")
    with open(gemmini_makefile_path, "w") as file:
        file.write(germmini_make_file(filename))
        print("File content replaced successfully.")

    print("Building gemmini-rocc-tests/build.sh to include benchmark ")
    try:
        result = subprocess.run(
            [gemmini_build_path], capture_output=True, text=True, shell=True
        )
    except FileNotFoundError:
        print(f"The script {gemmini_build_path} does not exist.")
    except subprocess.CalledProcessError as e:
        print(f"Script failed with return code {e.returncode}")


def run_gemmini(filename):
    print("Running gemmini/scripts/run-vcs.sh ")
    try:
        result = subprocess.run(
            [gemmini_run_script_path, filename],
            capture_output=True,
            text=True,
            shell=True,
        )
        output = result.stdout.strip().split("\n")
        test_name, kernel_exec, e2e_exec = output[-3:]
        kernel_time, *kernel_std = kernel_exec.split()
        e2e_time, *e2e_std = e2e_exec.split()
        print(f"Finished executing {filename}")
        return (float(kernel_time), None, float(e2e_time), None)
    except subprocess.CalledProcessError as e:
        print(f"Execution failed for {filename}: {e}")
        exit(1)


def run_file(filename):
    if filename not in all_test:
        print(f"Input benchmark name {filename} is invalid for this backend")
        exit(1)

    if filename in (blend_test_name + llama_test_name) and filename not in (
        gemmini_blend_func_names + gemmini_llama_func_names
    ):
        print(f"Input benchmark name {filename} is invalid for this backend")
        exit(1)

    if filename in gemmini_not_comp:
        print(f"Input benchmark name {filename} is invalid for this backend")
        exit(1)

    cpp_exec_files = find_file(cpp_dir, filename + "_O3_GEM")
    cpp_files = find_file(cpp_dir, filename + "_gemmini_baseline.cc")

    gemmini_files = find_file(gemmini_dir, filename + "_gemmini.c")

    cpp_exec_file = ""

    if not cpp_exec_files:
        print(
            f"Expected {filename}_O3_GEM not found in {cpp_dir}. Trying to compile the C++ file."
        )

        if not cpp_files:
            print(f"Error: {filename}_gemmini_baseline.cc not found in {cpp_dir}")
            exit(1)
        else:
            cpp_exec_file = compile_cpp(cpp_files[0], filename + "_O3_GEM")
            print("Successfully compiled C++")
    else:
        cpp_exec_file = cpp_exec_files[0]

    # Compile Germmini c file
    if not gemmini_files:
        print(f"Expected {filename}_gemmini.c not found in {cpp_dir}.")

    print(f"Setting up to run {filename}_gemmini.c")
    setup_gemmini(gemmini_files[0], filename + "_gemmini.c")
    print(f"Successfully setup {filename}_gemmini.c")

    cpp_kernel_time, cpp_kernel_std, cpp_e2e_time, cpp_e2e_std = execute_file(
        cpp_exec_file
    )

    # Execute Germmini c file
    gemmini_kernel_cycle, _, gemmini_e2e_cycle, _ = run_gemmini(filename + "_gemmini.c")

    print(f"{filename} Gemmini speedup test")
    print(f"C++ Kernel Execution Time: {cpp_kernel_time} ms +/- {cpp_kernel_std}")
    print(f"Gemmini Kernel Cycle Count: {gemmini_kernel_cycle}")
    gemmini_kernel_runtime = (
        gemmini_runtime_conversion.get(filename, 10000)
        * gemmini_kernel_cycle
        / (10**9)
        * 1000
    )
    print(f"Gemmini Kernel Computed Runtime: {gemmini_kernel_runtime} ms")
    print(f"Speedup: {cpp_kernel_time / gemmini_kernel_runtime:.2f}X")
    print(f"C++ E2E Execution Time: {cpp_e2e_time} ms +/- {cpp_e2e_std}")
    print(f"Gemmini E2E Cycle Count: {gemmini_e2e_cycle}")
    gemmini_e2e_runtime = (
        gemmini_runtime_conversion.get(filename, 10000)
        * gemmini_e2e_cycle
        / (10**9)
        * 1000
    )
    print(f"Gemmini E2e Computed Runtime: {gemmini_e2e_runtime} ms")
    print(f"Speedup: {cpp_e2e_time / gemmini_e2e_runtime:.2f}X")
    return cpp_kernel_time / gemmini_kernel_runtime, cpp_e2e_time / gemmini_e2e_runtime


def get_gemmini_speedup(benchmark_name: str):
    if benchmark_name == "ALL":
        all_e2e_speedup = []
        all_kernel_speedup = []
        for test in all_test:
            if benchmark_name in (
                blend_test_name + llama_test_name
            ) and benchmark_name not in (
                gemmini_blend_func_names + gemmini_llama_func_names
            ):
                continue

            if benchmark_name in gemmini_not_comp:
                continue

            kernel_speedup, e2e_speedup = run_file(test)
            all_e2e_speedup.append(e2e_speedup)
            all_kernel_speedup.append(kernel_speedup)
        all_e2e_speedup = np.array(all_e2e_speedup)
        all_kernel_speedup = np.array(all_kernel_speedup)
        print(
            f"Average kernel speedup of all in Gemmini is: {np.mean(all_kernel_speedup)}"
        )
        print(f"Average E2E speedup of all in Gemmini is: {np.mean(all_e2e_speedup)}")
    else:
        run_file(benchmark_name)


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python gemmini_speedup_exec.py <benchmark name>")
        exit(1)

    get_gemmini_speedup(sys.argv[1])
