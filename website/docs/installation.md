---
sidebar_position: 1
---

# Installation
Let's get started by installing Metalift and its dependencies!

## Get the Metalift source code
First, you'll need to clone the Metalift repository (we are working on making Metalift available as a Python package in the near future):

```bash
git clone https://github.com/metalift/metalift.git
cd metalift
```

## Install the dependencies
- [Racket](https://racket-lang.org) as the underlying language for the synthesis engine
- [Rosette](https://github.com/emina/rosette), the synthesis engine that Metalift uses
  - For maximum performance on Apple Silicon machines, you may want to replace the built-in Intel binary for Z3 with a native build
- [CVC5](https://cvc5.github.io/), the theorem prover that Metalift uses to check candidate solutions
- [Clang/LLVM 11](https://llvm.org), to compile input programs to LLVM IR for analysis
- [CMake](https://cmake.org/), to build the custom LLVM pass

### Install Python Dependencies
We use [Poetry](https://python-poetry.org/) for dependency management. To set up the environment, simply install Poetry, run `poetry install`, and then `poetry shell` to enter an environment with the dependencies installed.

### Installation using Nix
If you use [Nix](https://nixos.org/), you can automatically get all these dependencies using the `flake.nix` definition in the base directory of the Metalift repository. Once you've got Nix installed, you'll need to enable [flakes](https://nixos.wiki/wiki/Flakes).

```
$ nix develop
$ # all dependencies are available!
```

## Build the custom LLVM pass
Metalift makes use of a custom LLVM pass to organize the basic blocks in a way that is easier to analyze. To build the pass, we'll use CMake:

```bash
cd llvm-pass
mkdir build
cd build
cmake ..
make
cd ../..
```

Now, we are ready to start building verified lifting systems with Metalift!
