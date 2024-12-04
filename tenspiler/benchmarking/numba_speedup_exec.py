import os
import sys

from tenspiler.benchmarking.utils import *

python_dir = os.path.join(parent_path, "numba")


def run_file(filename):
    if filename not in all_test:
        print(f"Input benchmark name {filename} is invalid for this backend")
        exit(1)

    # cpp_exec_files = find_file(cpp_dir, filename + "_O3")
    # cpp_files = find_file(cpp_dir, filename + ".cc")
    python_files = find_file(python_dir, filename + "_numba.py")

    # cpp_exec_file = ""
    python_file = ""

    # if not cpp_exec_files:
    #     print(
    #         f"Expected {filename}_O3 not found in {cpp_dir}. Trying to compile the C++ file."
    #     )
    #     if not cpp_files:
    #         print(f"Error: {filename}.cc not found in {cpp_dir}")
    #         exit(1)
    #     else:
    #         cpp_exec_file = compile_cpp(cpp_files[0])
    #         print("Successfully compiled C++")
    # else:
    #     cpp_exec_file = cpp_exec_files[0]

    if not python_files:
        print(f"Error: {filename}_np.py not found in {python_dir}")
        exit(1)
    else:
        python_file = python_files[0]

    # cpp_kernel_time, cpp_kernel_std, cpp_e2e_time, cpp_e2e_std = execute_file(
    #     cpp_exec_file
    # )
    py_kernel_time, py_kernel_std, py_e2e_time, py_e2e_std = execute_file(python_file)

    print(f"{filename} Kernel Execution Time: {py_kernel_time} ms +/- {py_kernel_std} ")
    # print(f"C++ Kernel Execution Time: {cpp_kernel_time} ms +/- {cpp_kernel_std}")
    print(f"Numba Kernel Execution Time: {py_kernel_time} ms +/- {py_kernel_std}")
    # print(f"Speedup: {cpp_kernel_time / py_kernel_time:.2f}X")
    # print(f"C++ E2E Execution Time: {cpp_e2e_time} ms +/- {cpp_e2e_std}")
    print(f"Numba E2E Execution Time: {py_e2e_time} ms +/- {py_e2e_std}")
    # print(f"Speedup: {cpp_e2e_time / py_e2e_time:.2f}X")
    # return cpp_kernel_time / py_kernel_time, cpp_e2e_time / py_e2e_time


def get_numba_speedup(benchmark_name: str) -> None:
    if benchmark_name == "ALL":
        all_e2e_speedup = []
        all_kernel_speedup = []
        for test in all_test:
            run_file(test)
        #     kernel_speedup, e2e_speedup = run_file(test)
        #     all_e2e_speedup.append(e2e_speedup)
        #     all_kernel_speedup.append(kernel_speedup)
        # all_e2e_speedup = np.array(all_e2e_speedup)
        # all_kernel_speedup = np.array(all_kernel_speedup)
        # print(
        #     f"Average kernel speedup of all in Numba is: {np.mean(all_kernel_speedup)}"
        # )
        # print(f"Average E2E speedup of all in Numba is: {np.mean(all_e2e_speedup)}")
    else:
        run_file(benchmark_name)


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python numba_speedup_exec.py <benchmark name>")
        exit(1)

    get_numba_speedup(sys.argv[1])
