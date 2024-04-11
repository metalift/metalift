import os
import runpy
import sys
from os.path import dirname, join, basename
from pathlib import Path

from tenspiler.codegen.tensorflow_codegen import tensorflow_codegen
from tenspiler.codegen.utils import DataType

# def compile_all(compile_dirs):
#     for d in compile_dirs:
#         cwd = os.getcwd()
#         os.chdir(d)
#         subprocess.run(["./compile-add-blocks.sh", "ALL"], check=True)
#         os.chdir(cwd)
#         print("successfully compiled all input files")

# compile_dirs = ["tenspiler/llama/cpp/", "tenspiler/blend/cpp/for_synthesis/", "tenspiler/c2taco/cpp/"]
# compile_all(compile_dirs)

def find_all_drivers(driver_dirs):
    driver_files = []
    for root_dir in driver_dirs:
        for dirpath, dirnames, filenames in os.walk(root_dir):
            for filename in filenames:
                if filename.endswith("_driver.py"):
                    full_path = join(dirpath, filename)
                    driver_files.append(full_path)
    return driver_files

# driver_dirs = ["tenspiler/llama/holing/driver/", "tenspiler/blend/holing/driver/", "tenspiler/c2taco/holing/driver/"]
driver_dirs = ["tenspiler/c2taco/holing/driver/"]
driver_files = find_all_drivers(driver_dirs)

stored_path = "./tenspiler/benchmarking/tensorflow/"

for script_path in driver_files:
    script_dir = dirname(script_path)
    script_basename = basename(script_path)
    script_name, _ = script_basename.rsplit('.', 1)

    if script_dir not in sys.path:
        sys.path.append(script_dir)

    result = runpy.run_module(script_name, run_name="__main__")

    if script_dir in sys.path:
        sys.path.remove(script_dir)

    driver = result.get('driver')

    #NOTE: All c2taco uses full integer
    tensorflow_code = tensorflow_codegen(driver.get_actual_ps_fn_decl(), driver.synthesized_fns, DataType.FULL_INT)

    e2e_fn_name = f"{driver.get_actual_ps_fn_decl().name()[:-3]}_tf"
    kernel_fn_name = e2e_fn_name + "_kernel"

    #NOTE: this is for c2taco or blend only since they use the imagenet dataset
    setup_code = f"""
####### more import statements for benchmarking ########
import time
import cv2
import os
import numpy as np

####### setup for benchmarking ########
rng = np.random.default_rng(1)

folder = "./data/"

img_files = [os.path.join(folder, f) for f in os.listdir(folder) if os.path.isfile(os.path.join(folder, f))]

bases = []
actives = []

for _file in img_files:
    img = cv2.imread(_file, cv2.IMREAD_GRAYSCALE).astype(np.uint8)
    rnd = (rng.random(img.shape, dtype = np.float32) * 255).astype(np.uint8)
    bases.append(img)
    actives.append(rnd)
""" 
    
    tensorflow_code_timing = tensorflow_code + setup_code + """
####### runner. need to manually update for each file ########  
runs = 10
times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(bases)):
        b = bases[i].flatten().astype(np.int32)
        a = actives[i].flatten().astype(np.int32)
        b = bases[i].astype(np.int32)
        a = actives[i].astype(np.int32)
        rand_f = rng.integers(low=0, high=np.iinfo(np.int32).max + 1, size=b.shape, dtype=np.int32)
        s = rng.integers(low=0, high=np.iinfo(np.int32).max + 1).astype(np.int32)

        with tf.device('/GPU:0'):
            b = tf.convert_to_tensor(b, np.int32)
            a = tf.convert_to_tensor(a, np.int32)
            rand_f = tf.convert_to_tensor(rand_f, np.int32)

            n, = b.shape
            m, n = b.shape

            start_time = time.perf_counter()
            
            
            end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)   
"""

    tensorflow_code_timing_kernel = tensorflow_code_timing + f"""
print("{kernel_fn_name}")
print(f"{{np.average(times)}} {{np.std(times)}}") 
"""
    
    tensorflow_code_e2e_timing = tensorflow_code_timing + f"""
print("{e2e_fn_name}")
print(f"{{np.average(times)}} {{np.std(times)}}") 
"""
    
    path_obj = Path(script_path)
    folder_name = path_obj.parent.name if path_obj.parent.name != "driver" else ""
    
    kernel_filename = join(stored_path, folder_name, f"{kernel_fn_name}.py")
    e2e_filename = join(stored_path, folder_name, f"{e2e_fn_name}.py")

    kernel_filepath = Path(kernel_filename)
    e2e_filepath = Path(e2e_filename)

    kernel_filepath.parent.mkdir(parents=True, exist_ok=True)
    e2e_filepath.parent.mkdir(parents=True, exist_ok=True)

    with kernel_filepath.open('w') as file:
        file.write(tensorflow_code_timing_kernel)

    # with e2e_filepath.open('w') as file:
    #     file.write(tensorflow_code_e2e_timing)    



    