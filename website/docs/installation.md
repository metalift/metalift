---
sidebar_position: 1
---

# Installation
Let's get started by installing Metalift and its dependencies!

## Get the Metalift source code
First, you'll need to clone the Metalift repository:

```bash
git clone https://github.com/metalift/metalift.git
cd metalift
```

## Install the dependencies
- [Racket](https://racket-lang.org) as the underlying language for the synthesis engine
- [Rosette](https://github.com/emina/rosette), the synthesis engine that Metalift uses
  - For maximum performance on Apple Silicon machines, you may want to replace the built-in Intel binary for Z3 with a native build
- [CVC5](https://cvc5.github.io/), the theorem prover that Metalift uses to check candidate solutions
- [Clang/LLVM 11](https://llvm.org), to compile input programs to LLVM IR for analysis (currently support LLVM 11)
- [CMake](https://cmake.org/), to build the custom LLVM pass

### Install Python Dependencies
We use [Poetry](https://python-poetry.org/) for dependency management. To set up the environment, simply install Poetry, run `poetry install`, and then `poetry shell` to enter an environment with the dependencies installed.

### Installation using Nix
To get a development environment up and running, one option is to use [Nix](https://nixos.org/), which can automatically pull and build the necessary dependencies. First, you'll need to [install Nix](https://nixos.org/download.html). Note that this _will_ require temporary root access as Nix sets up a daemon to handle builds, and will set up a separate volume for storing build artifacts if on macOS.

Once you've got Nix installed, you'll need to enable [flakes](https://nixos.wiki/wiki/Flakes).

Then, all you have to do is navigate to the Metalift directory and run the following command:
```bash
$ nix develop
$ # all dependencies are available!
```

This will build all of Metalift's dependencies and drop you into a temporary shell with all the dependencies available.

**Note**: you still will need to install Racket and Rosette separately. There _is_ a solution for doing this through Nix, but it requires [nix-ld](https://github.com/Mic92/nix-ld) to be installed and is generally not recommended unless you run NixOS.

## Build the custom LLVM pass
After LLVM is installed, use the following instructions to build our custom LLVM pass. 
Metalift uses this pass to organize the basic blocks in a way that is easier to analyze. To build this pass, we'll use CMake:

```bash
cd llvm-pass
mkdir build
cd build
cmake ..
make
cd ../..
```

(Optional) If you want to try running this pass, first generate LLVM bytecode from your source file, then do this:
````angular2
opt -load build/addEmptyBlocks/libAddEmptyBlocksPass.so -addEmptyBlock -S <.ll name>
````
This pass is called in `tests/compile-add-blocks`.

Now, we are ready to start building verified lifting systems with Metalift!
