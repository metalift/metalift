import os
import subprocess

from tenspiler.codegen.numpy_codegen import numpy_codegen

# All commands should be run from root directory by default
os.chdir('../..')

compile_dir = ["tenspiler/llama/cpp/", "tenspiler/blend/cpp/for_synthesis/", "tenspiler/c2taco/cpp/"]

for d in compile_dir:
    cwd = os.getcwd()
    os.chdir(d)
    subprocess.run(["./compile-add-blocks.sh", "ALL"], check=True)
    os.chdir(cwd)
    print("successfully compiled all input files")
    