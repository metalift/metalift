<p align="center"><img width="800" src="https://github.com/metalift/metalift/raw/main/logo.png"/></p>
<p align="center"><i>A program synthesis framework for verified lifting applications</i></p>

# Get Started at [metalift.pages.dev](https://metalift.pages.dev)

See [tests](https://github.com/metalift/metalift/tree/main/tests) folder for test cases. 
Check out any of the python files in that folder to see how to define
your target language and build your own lifting based compiler. 
Do not use `main.py`.

We currently support [Rosette](https://emina.github.io/rosette/) (and [cvc5](https://cvc5.github.io/) but cvc5 has been flaky) as the synthesis backend, and [Z3](https://github.com/Z3Prover/z3) as the verifier.

### LLVM instructions

**We currently support LLVM 11**

Run the following to build the LLVM pass for processing branch instructions (works for LLVM 11):
````angular2
cd llvm-pass
mkdir build
cd build
cmake ..
make 
cd ..
```` 
Then run it with:
````angular2
opt -load build/addEmptyBlocks/libAddEmptyBlocksPass.so -addEmptyBlock -S <.ll name>
````
This pass is called in `tests/compile-add-blocks`.

### Deprecated instructions from earlier version

To run synthesis, build [CVC5](https://github.com/cvc5/cvc5) from source, run `configure` with `debug` and then build.

Then run metalift from `main.py`.

Example synthesis usage: `main.py tests/while4.ll tests/while4-grammar.sl tests/out.smt test tests/while4.loops <path to cvc5>`

Example verification usage (using pre-generated answer): `main.py tests/while4.ll tests/while4-ans.smt tests/out.smt test tests/while4.loops`
This prints the verification file to out.smt that can be run using an external solver (e.g., z3)

## Set up with Nix
To get a development environment up and running, one option is to use [Nix](https://nixos.org/), which can automatically pull and build the necessary dependencies. First, you'll need to [install Nix](https://nixos.org/download.html). Note that this _will_ require temporary root access as Nix sets up a daemon to handle builds, and will set up a separate volume for storing build artifacts if on macOS.

Once you've got Nix installed, you'll need to enable [flakes](https://nixos.wiki/wiki/Flakes).

Then, all you have to do is navigate to the Metalift directory and run the following command:
```bash
$ nix develop
```

This will build all of Metalift's dependencies and drop you into a temporary shell with all the dependencies available.

**Note**: you still will need to install Racket and Rosette separately. There _is_ a solution for doing this through Nix, but it requires [nix-ld](https://github.com/Mic92/nix-ld) to be installed and is generally not recommended unless you run NixOS.

## Install Python Dependencies
We use [Poetry](https://python-poetry.org/) for dependency management. To set up the environment, simply install Poetry, run `poetry install`, and then `poetry shell` to enter an environment with the dependencies installed.
