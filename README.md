# LLMLift
LLMLift is an LLM-based approach for building verified-lifting tools. LLMLift builds over [MetaLift](https://metalift.pages.dev/) by replacing its symbolic synthesis engine with an LLM.

Check out the full paper [here](https://openreview.net/forum?id=spwE9sLrfg), accepted at NeurIPS 2024.

## Getting started

### Installation

#### Get source code
First, clone the MetaLift repository with branch `llmlift`.
```bash
git clone --branch llmlift https://github.com/metalift/metalift.git
```

#### Install dependencies
LLMLift supports both bounded verification and full verification. Bounded verification is done using Rosette's verification API and full verification is performed using an SMT solver (cvc5).
For bounded verification, install [Racket](https://racket-lang.org) and [Rosette](https://github.com/emina/rosette), and for full verification, install [cvc5](https://cvc5.github.io/).

LLMLift can translate source code written in C++, and requires the following dependencies for generating the specification (VC).
  - [Clang/LLVM 11](https://llvm.org), to compile input programs to LLVM IR for analysis.
  - [CMake](https://cmake.org/), to build the custom LLVM pass.

#### Install Python dependencies
We use [Poetry](https://python-poetry.org/) for dependency management. To set up the environment, simply install Poetry through `pip install poetry`. Then, run `poetry install` and `poetry shell` to enter an environment with dependencies installed.

#### Build the custom LLVM pass
LLMLift makes use of a custom LLVM pass to organize the basic blocks in a way that is easier to analyze. To build the pass, we'll use CMake:

```bash
cd llvm-pass
mkdir build
cd build
cmake ..
make
cd ../..
```

#### Install pre-commit Hooks
We use [pre-commit](https://pre-commit.com/) to enforce code style and formatting. To install the pre-commit hooks, run `pre-commit install`.

## Running Benchmarks
We currently support Claude, Gemini, and GPT as the LLM model for synthesis. You can use any of these three models by setting their corresponding API keys (`OPENAI_API_KEY`, `CLAUDE_API_KEY`, `GEMINI_API_KEY`) in a `.env` file.

As examples, we include two sets of benchmarks, the **blend** benchmarks, which include 12 open-source implementations of blending modes in Photoshop, and the **Llama** benchmarks, which consist of 11 C++ inference kernels of Llama2 that capture operations such as computing activations, attention mechanisms, and layer norms. The benchmarks are available in the [`tenspiler/blend/llm`](./tenspiler/blend/llm) and the [`tenspiler/llama/llm`](./tenspiler/llama/llm) directories, respectively. Scripts for end-to-end synthesis and verification of the benchmarks live under the `benchmarks/(blend|llama)/llm/driver/` directories can be run using the following commands:

```bash
python3 tenspiler/(blend|llama)/llm/driver/{benchmark_name}_driver.py
```