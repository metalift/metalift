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
