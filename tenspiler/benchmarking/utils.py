import glob
import os
import subprocess

parent_path = "./tenspiler/benchmarking/"

cpp_dir = os.path.join(parent_path, "cpp")
utils_filepath = os.path.join(cpp_dir, "utils.cc")

COMPILER = "h5c++"
FLAG = "-O3"
INCLUDE = f"-I/usr/include/opencv4 -I{cpp_dir}"
LINK = "-lopencv_highgui -lopencv_core -lopencv_imgproc -lhdf5_cpp -lhdf5 "

PYTHON_CMD = ["poetry", "run", "python"]

blend_test_name = [
    "color_burn_8",
    "color_dodge_8",
    "darken_blend_8",
    "dissolve_blend_8",
    "lighten_blend_8",
    "linear_burn_8",
    "linear_dodge_8",
    "multiply_blend_8",
    "normal_blend_8",
    "normal_blend_f",
    "overlay_blend_8",
    "screen_blend_8",
]

llama_test_name = [
    "matmul",
    "rmsnorm_part1",
    "rmsnorm_part2",
    "softmax_part1",
    "softmax_part2",
    "softmax_part3",
    "softmax_part4",
    "transformer_part1",
    "transformer_part2",
    "transformer_part3",
    "transformer_part4",
]

darknet_test_name = [
    "mag_array",
    "matrix_add_matrix",
    "mse_array",
    "mult_add_into_cpu",
    "ol_l2_cpu1",
    "ol_l2_cpu2",
    "scale_array",
    "scale_matrix",
    "sum_array",
    "translate_array",
]


utdsp_test_name = ["fir_small", "lmsfir1", "lmsfir2"]
all_test = blend_test_name + llama_test_name + darknet_test_name + utdsp_test_name


def execute_file(filepath):
    if filepath.endswith(".py"):
        command = [*PYTHON_CMD, filepath]
    elif os.access(filepath, os.X_OK):
        command = [filepath]
    else:
        print(f"Error: {filepath} is not executable and is not a Python file.")
        exit(1)
    print(f"Executing {filepath}")
    try:
        result = subprocess.run(command, capture_output=True, text=True, check=True)
        output = result.stdout.strip().split("\n")
        test_name, e2e_exec, kernel_exec = output[-3:]
        kernel_time, *kernel_std = kernel_exec.split()
        e2e_time, *e2e_std = e2e_exec.split()
        print(f"Finished executing {filepath}")
        return (
            float(kernel_time),
            kernel_std[0] if kernel_std else None,
            float(e2e_time),
            e2e_std[0] if e2e_std else None,
        )
    except subprocess.CalledProcessError as e:
        print(f"Execution failed for {filepath}: {e}")
        exit(1)


def compile_cpp(source_path, output_path=None):
    if not output_path:
        output_path = source_path.replace(".cc", "_O3")
    compile_command = [
        COMPILER,
        FLAG,
        INCLUDE,
        source_path,
        utils_filepath,
        LINK,
        "`pkg-config opencv4 --cflags --libs`",
        "-o",
        output_path,
    ]

    try:
        subprocess.run(compile_command, check=True)
        print(f"Compiled {source_path} successfully.")
        return output_path
    except subprocess.CalledProcessError:
        print(f"Failed to compile {source_path}.")
        exit(1)


def find_file(directory, pattern):
    return glob.glob(os.path.join(directory, "**", pattern), recursive=True)
