See [tests](https://github.com/metalift/metalift/tree/llvm/tests) folder for test cases. 
Check out any of the python files in that folder to see how to define
your target language and build your own lifting based compiler. 
Do not use `main.py`.

We currently support [cvc5](https://cvc5.github.io/) as the synthesis backend (with plans to include [Rosette](https://emina.github.io/rosette/)) 
and [Z3](https://github.com/Z3Prover/z3) as the verifier.

### LLVM instructions

Run the following to build the LLVM pass for processing branch instructions (works on LLVM 10):
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


