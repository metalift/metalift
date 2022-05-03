---
sidebar_position: 1
---

# Installation
Let's get started by installing Metalift and it's dependencies!

## What you'll need
- [Racket](https://racket-lang.org) as the underlying language for the synthesis engine
- [Rosette](https://github.com/emina/rosette), the synthesis engine that Metalift uses
  - For maximum performance on Apple Silicon machines, you may want to replace the built-in Intel binary for Z3 with a native build
- [CVC5](https://cvc5.github.io/), the theorem prover that Metalift uses to check candidate solutions
- [Clang/LLVM 11](https://llvm.org), to compile input programs to LLVM IR for analysis
- [CMake](https://cmake.org/), to build the custom LLVM pass

### Installation using Nix
If you use [Nix](https://nixos.org/), you can automatically get all these dependencies using the `shell.nix` definition in the base directory of the Metalift repository.

```
$ nix-shell
$ # all dependencies are available!
```

## Build our fork of `llvmlite`
We use a modified version of `llvmlite` to parse and analyze LLVM IR. To build the fork, you'll need to start by cloning the submodule:

```bash
$ git submodule update --init --recursive
```

Then, you can build the fork:

```bash
$ cd llvmlite
$ python setup.py build
$ cd ..
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
