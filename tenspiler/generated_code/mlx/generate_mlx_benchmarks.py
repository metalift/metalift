import os
import runpy
import sys
from os.path import basename, dirname, join
from pathlib import Path

from tenspiler.codegen.mlx_codegen import mlx_codegen
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

stored_path = "./tenspiler/generated_code/mlx/"

def generate_benchmark(benchmark_name):
    if benchmark_name not in all_test:
        print(f"Benchmark name {benchmark_name} is not in predefined benchmark name list!")
        exit(1)

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

    mlx_code = mlx_codegen(
        driver.get_actual_ps_fn_decl(), driver.synthesized_fns, data_type
    )

    print(f"Successfully generated code for {benchmark_name}")

    e2e_fn_name = f"{driver.get_actual_ps_fn_decl().name()[:-3]}_mx"

    # NOTE: The following if only needed for generating benchmark executables and need manual effort in connecting input.
    #     setup_code = f"""
    # ####### more import statements for benchmarking ########
    # import numpy as np
    # import time
    # import cv2
    # import os

    # ####### setup for benchmarking ########
    # rng = np.random.default_rng(1)

    # folder = "./tenspiler/data/data_sampled"

    # img_files = [os.path.join(folder, f) for f in os.listdir(folder) if os.path.isfile(os.path.join(folder, f))]

    # bases = []
    # actives = []

    # for _file in img_files:
    #     img = cv2.imread(_file, cv2.IMREAD_GRAYSCALE).astype(np.uint8)
    #     rnd = (rng.random(img.shape, dtype = np.float32) * 255).astype(np.uint8)
    #     bases.append(img)
    #     actives.append(rnd)
    # """

    #     mlx_code_timing = mlx_code + setup_code + """
    # ####### runner. need to manually update for each file ########
    # runs = 10
    # times = []
    # for _ in range(runs):
    #     total_time = 0
    #     for i in range(len(bases)):

    #         start_time = time.perf_counter()

    #         end_time = time.perf_counter()
    #         total_time += (end_time - start_time) * 1000

    #     times.append(total_time)

    # times = np.array(times)
    # """

    mlx_code_e2e_timing = mlx_code
    #     mlx_code_e2e_timing = mlx_code_timing + f"""
    # print("{e2e_fn_name}")
    # print(f"{{np.average(times)}} {{np.std(times)}}")
    # """

    path_obj = Path(script_path)
    folder_name = path_obj.parent.name if path_obj.parent.name != "driver" else ""

    if benchmark_name in blend_test_name:
        folder_name = "blend"
    elif benchmark_name in llama_test_name:
        folder_name = "llama"
    
    e2e_filename = join(stored_path, folder_name, f"{e2e_fn_name}.py")

    e2e_filepath = Path(e2e_filename)

    e2e_filepath.parent.mkdir(parents=True, exist_ok=True)

    with e2e_filepath.open("w") as file:
        file.write(mlx_code_e2e_timing)

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
        print("Usage: python generate_mlx_benchmarks.py <benchmark name>")
        exit(1)

    generate_benchmarks(sys.argv[1])