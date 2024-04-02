# Tenspiler
Tenspiler is a verified lifting-based compiler that translates sequential programs written in C++ into tensor operations to leverage high performance tensor processing infrastructures such as deep learning frameworks and specialized hardware accelerators. Currently, Tenspiler supports six distinct software or backend backends including NumPy, TensorFlow, PyTorch, MLX (an ML framework on Apple silicon), TPC-C (C-based programming language for Intel’s
Gaudi processor), and Gemmini (an open-source neural network accelerator generator).



## Getting started

### Installation
Let's get started by installing Metalift and its dependencies!

#### Get the Metalift source code
First, clone the Tenspiler repository:
<!-- TODO(jie): fix the naming -->
```bash
git clone https://github.com/tenspiler/tenspiler.git
cd tenspiler
```

#### Install the dependencies
- [Racket](https://racket-lang.org) as the underlying language for the synthesis engine
- [Rosette](https://github.com/emina/rosette), the synthesis engine that Tenspiler uses
  - For maximum performance on Apple Silicon machines, you may want to replace the built-in Intel binary for Z3 with a native build
- [CVC5](https://cvc5.github.io/), the theorem prover that Metalift uses to check candidate solutions
- [Clang/LLVM 11](https://llvm.org), to compile input programs to LLVM IR for analysis
- [CMake](https://cmake.org/), to build the custom LLVM pass

#### Install Python Dependencies
We use [Poetry](https://python-poetry.org/) for dependency management. To set up the environment, simply install Poetry, run `poetry install`, and then `poetry shell` to enter an environment with the dependencies installed.

#### Build the custom LLVM pass
Metalift makes use of a custom LLVM pass to organize the basic blocks in a way that is easier to analyze. To build the pass, we'll use CMake:

```bash
cd llvm-pass
mkdir build
cd build
cmake ..
make
cd ../..
```

#### Install Pre-commit Hooks
We use [pre-commit](https://pre-commit.com/) to enforce code style and formatting. To install the pre-commit hooks, run `pre-commit install`.

## Running Benchmarks
We have evaluated Tenspiler on two sets of benchmarks, the **blend** benchmarks, which include 12 open-source implementations of blending modes in Photoshop, and the **Llama** benchmarks, which consist of 11 C++ inference kernels of Llama2 that capture operations such as computing activations, attention mechanisms, and layer norms. The benchmarks are available in the `tenspiler/benchmarks/blend/` and the `tenspiler/benchmarks/llama/` directories, respectively. Scripts for end-to-end synthesis and verification of the benchmarks live under the `benchmarks/{blend or llama}/holing/driver/` directories can be run using the following commands:

```bash
python3 tenspiler/{blend or llama}/holing/driver/{benchmark_name}_driver.py
```

To invoke code generation for your synthesized and verified solutions, simply import and invoke your desired code generation functions. For example, to generate MLX code for the `darken_blend_8` benchmark, you can add the following to the end of `tenspiler/blend/holing/driver/darken_blend_8_driver.py`

```bash
mlx_codegen(driver.get_actual_ps_fn_decl(), driver.synthesized_fns)
```

## TensIR
Tenspiler is able to lift whatever is expressible in TensIR, an intermediate language that captures many tensor operations. The full grammar can be found in the figure below.


## Adding a new backend
To add a new backend to Tenspiler, you simply need to add a code generation file named `{your backend name}_codegen.py` in the `tenspiler/codegen/` directory. You should only need to write simple syntax-driven translation rules to translate `tensIR` program into the target backend. Follow [the MLX code generation file](tenspiler/codegen/mlx_codegen.py) as an example!
