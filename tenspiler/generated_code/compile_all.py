import os
import subprocess


def compile_all(compile_dirs):
    for d in compile_dirs:
        cwd = os.getcwd()
        os.chdir(d)
        subprocess.run(["./compile-add-blocks.sh", "ALL"], check=True)
        os.chdir(cwd)
        print("successfully compiled all input files")


compile_dirs = [
    "tenspiler/llama/cpp/",
    "tenspiler/blend/cpp/for_synthesis/",
    "tenspiler/c2taco/cpp/",
]
compile_all(compile_dirs)
