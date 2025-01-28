import os
import runpy
import sys
from os.path import basename, dirname, join
from pathlib import Path

from tenspiler.codegen.gaudi_codegen import gaudi_codegen
from tenspiler.codegen.mlx_codegen import mlx_codegen
from tenspiler.codegen.numpy_codegen import numpy_codegen
from tenspiler.codegen.pytorch_codegen import pytorch_codegen
from tenspiler.codegen.tensorflow_codegen import tensorflow_codegen
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

stored_path = "./tenspiler/generated_code/pytorch/"


def generate_benchmark(benchmark_name):
    if benchmark_name not in all_test:
        print(
            f"Benchmark name {benchmark_name} is not in predefined benchmark name list!"
        )
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
    stored_path = "./tenspiler/generated_code/pytorch/"
    torch_code = pytorch_codegen(
        driver.get_actual_ps_fn_decl(), driver.synthesized_fns, data_type
    )

    print(f"Successfully generated code for {benchmark_name}")

    e2e_fn_name = f"{driver.get_actual_ps_fn_decl().name()[:-3]}_torch"
    kernel_fn_name = e2e_fn_name + "_kernel"

    # NOTE: The following if only needed for generating timing executables and need manual effort in connecting input.
    #     setup_code = f"""
    # ####### more import statements for benchmarking ########
    # import time
    # import cv2
    # import os
    # import numpy as np

    # ####### setup for benchmarking ########
    # rng = np.random.default_rng(1)
    # if not torch.cuda.is_available():
    #   print("CUDA is not available on this system")
    # device = 'cuda' if torch.cuda.is_available() else 'cpu'
    # cpu = 'cpu'

    # folder = "./data/"

    # img_files = [os.path.join(folder, f) for f in os.listdir(folder) if os.path.isfile(os.path.join(folder, f))]

    # bases = []
    # actives = []

    # for _file in img_files:
    #     img = cv2.imread(_file, cv2.IMREAD_GRAYSCALE).astype(np.uint8)
    #     rnd = (rng.random(img.shape, dtype = np.float32) * 255).astype(np.uint8)
    #     bases.append(img)
    #     actives.append(rnd)
    # """

    #     torch_code_timing = torch_code + setup_code + """
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

    #     torch_code_timing_kernel = torch_code_timing + f"""
    # print("{kernel_fn_name}")
    # print(f"{{np.average(times)}} {{np.std(times)}}")
    # """
    torch_code_e2e_timing = torch_code
    #     torch_code_e2e_timing = torch_code_timing + f"""
    # print("{e2e_fn_name}")
    # print(f"{{np.average(times)}} {{np.std(times)}}")
    # """

    path_obj = Path(script_path)
    folder_name = path_obj.parent.name if path_obj.parent.name != "driver" else ""

    if benchmark_name in blend_test_name:
        folder_name = "blend"
    elif benchmark_name in llama_test_name:
        folder_name = "llama"

    kernel_filename = join(stored_path, folder_name, f"{kernel_fn_name}.py")
    e2e_filename = join(stored_path, folder_name, f"{e2e_fn_name}.py")

    kernel_filepath = Path(kernel_filename)
    e2e_filepath = Path(e2e_filename)

    kernel_filepath.parent.mkdir(parents=True, exist_ok=True)
    e2e_filepath.parent.mkdir(parents=True, exist_ok=True)

    # with kernel_filepath.open('w') as file:
    #     file.write(torch_code_timing_kernel)

    with e2e_filepath.open("w") as file:
        file.write(torch_code_e2e_timing)

    print(f"Stored the genereted code into {e2e_filename}")

    # NOTE: All c2taco uses full integer
    # Tensorflow code
    stored_path = "./tenspiler/generated_code/tensorflow/"
    tensorflow_code = tensorflow_codegen(
        driver.get_actual_ps_fn_decl(), driver.synthesized_fns, data_type
    )

    print(f"Successfully generated code for {benchmark_name}")

    e2e_fn_name = f"{driver.get_actual_ps_fn_decl().name()[:-3]}_tf"
    kernel_fn_name = e2e_fn_name + "_kernel"

    # NOTE: The following if only needed for generating timing executables and need manual effort in connecting input.
    #     setup_code = f"""
    # ####### more import statements for benchmarking ########
    # import time
    # import cv2
    # import os
    # import numpy as np

    # ####### setup for benchmarking ########
    # gpus = tf.config.list_physical_devices('GPU')
    # if not gpus:
    #   print("No GPU is available")
    # rng = np.random.default_rng(1)

    # folder = "./data/"

    # img_files = [os.path.join(folder, f) for f in os.listdir(folder) if os.path.isfile(os.path.join(folder, f))]

    # bases = []
    # actives = []

    # for _file in img_files:
    #     img = cv2.imread(_file, cv2.IMREAD_GRAYSCALE).astype(np.uint8)
    #     rnd = (rng.random(img.shape, dtype = np.float32) * 255).astype(np.uint8)
    #     bases.append(img)
    #     actives.append(rnd)
    # """

    #     tensorflow_code_timing = tensorflow_code + setup_code + """
    # ####### runner. need to manually update for each file ########
    # runs = 10
    # times = []
    # for _ in range(runs):
    #     total_time = 0
    #     for i in range(len(bases)):
    #         b = bases[i].flatten().astype(np.int32)
    #         a = actives[i].flatten().astype(np.int32)
    #         b = bases[i].astype(np.int32)
    #         a = actives[i].astype(np.int32)
    #         rand_f = rng.integers(low=0, high=np.iinfo(np.int32).max + 1, size=b.shape, dtype=np.int32)
    #         s = rng.integers(low=0, high=np.iinfo(np.int32).max + 1).astype(np.int32)

    #         with tf.device('/GPU:0'):
    #             b = tf.convert_to_tensor(b, np.int32)
    #             a = tf.convert_to_tensor(a, np.int32)
    #             rand_f = tf.convert_to_tensor(rand_f, np.int32)

    #             n, = b.shape
    #             m, n = b.shape

    #             start_time = time.perf_counter()

    #             end_time = time.perf_counter()

    #         total_time += (end_time - start_time) * 1000

    #     times.append(total_time)

    # times = np.array(times)
    # """

    #     tensorflow_code_timing_kernel = tensorflow_code_timing + f"""
    # print("{kernel_fn_name}")
    # print(f"{{np.average(times)}} {{np.std(times)}}")
    # """
    tensorflow_code_e2e_timing = tensorflow_code
    #     tensorflow_code_e2e_timing = tensorflow_code_timing + f"""
    # print("{e2e_fn_name}")
    # print(f"{{np.average(times)}} {{np.std(times)}}")
    # """

    path_obj = Path(script_path)
    folder_name = path_obj.parent.name if path_obj.parent.name != "driver" else ""

    if benchmark_name in blend_test_name:
        folder_name = "blend"
    elif benchmark_name in llama_test_name:
        folder_name = "llama"

    kernel_filename = join(stored_path, folder_name, f"{kernel_fn_name}.py")
    e2e_filename = join(stored_path, folder_name, f"{e2e_fn_name}.py")

    kernel_filepath = Path(kernel_filename)
    e2e_filepath = Path(e2e_filename)

    kernel_filepath.parent.mkdir(parents=True, exist_ok=True)
    e2e_filepath.parent.mkdir(parents=True, exist_ok=True)

    # with kernel_filepath.open('w') as file:
    #     file.write(tensorflow_code_timing_kernel)

    with e2e_filepath.open("w") as file:
        file.write(tensorflow_code_e2e_timing)

    print(f"Stored the genereted code into {e2e_filename}")

    stored_path = "./tenspiler/generated_code/mlx/"

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

    # folder = "./data/"

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

    stored_path = "./tenspiler/generated_code/numpy/"
    numpy_code = numpy_codegen(
        driver.get_actual_ps_fn_decl(), driver.synthesized_fns, data_type
    )

    print(f"Successfully generated code for {benchmark_name}")

    e2e_fn_name = f"{driver.get_actual_ps_fn_decl().name()[:-3]}_np"

    # NOTE: The following if only needed for generating timing executables and need manual effort in connecting input.
    #     setup_code = f"""
    # ####### more import statements for benchmarking ########
    # import time
    # import cv2
    # import os

    # ####### setup for benchmarking ########
    # rng = np.random.default_rng(1)

    # folder = "./data/"

    # img_files = [os.path.join(folder, f) for f in os.listdir(folder) if os.path.isfile(os.path.join(folder, f))]

    # bases = []
    # actives = []

    # for _file in img_files:
    #     img = cv2.imread(_file, cv2.IMREAD_GRAYSCALE).astype(np.uint8)
    #     rnd = (rng.random(img.shape, dtype = np.float32) * 255).astype(np.uint8)
    #     bases.append(img)
    #     actives.append(rnd)
    # """

    #     numpy_code_timing = numpy_code + setup_code + """
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
    numpy_code_e2e_timing = numpy_code
    #     numpy_code_e2e_timing = numpy_code_timing + f"""
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
        file.write(numpy_code_e2e_timing)

    print(f"Stored the genereted code into {e2e_filename}")

    stored_path = Path("./tenspiler/generated_code/gaudi/")
    if benchmark_name not in all_test:
        print(
            f"Benchmark name {benchmark_name} is not in predefined benchmark name list!"
        )
        exit(1)

    if benchmark_name in llama_test_name or benchmark_name in [
        "vcopy",
        "mat1x3",
        "gemv",
    ]:
        print(
            f"Benchmark name {benchmark_name} is not supported in Gaudi backend with TPC-C. See PyTorch version."
        )
        return

    if benchmark_name in blend_test_name:
        data_type = DataType.UINT_8
    elif benchmark_name in llama_test_name:
        data_type = DataType.FLOAT
    else:
        data_type = DataType.INT32

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

    filepath = stored_path / folder_name / benchmark_name
    filepath.mkdir(parents=True, exist_ok=True)

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
        print("Usage: python generate_pytorch_benchmarks.py <benchmark name>")
        exit(1)

    generate_benchmarks(sys.argv[1])
