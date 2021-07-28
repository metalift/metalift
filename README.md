See [tests](https://github.com/metalift/metalift/tree/llvm/tests) folder for test cases

To run synthesis, build [CVC5](https://github.com/cvc5/cvc5) from source, run `configure` with `--debug-symbols` and then build.

Then run metalift from `main.py`.

Example usage: `main.py tests/while4.ll tests/while4-grammar.sl tests/out.smt test tests/while4.loops <path to cvc5>`
