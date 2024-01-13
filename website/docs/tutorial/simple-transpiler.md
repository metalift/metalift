---
sidebar_position: 1
---

# Building a Simple Transpiler

Now that we understand the basis of synthesis, let's try to build a simple transpiler. For this example imagine we have a target backend that has only a single instruction: [fused multiply add (FMA)](https://en.wikipedia.org/wiki/Multiply%E2%80%93accumulate_operation#Fused_multiply%E2%80%93add) for integers. Our goal is use Metalift to build a transpiler that can transpile the following C code to use the FMA instruction:

```cpp
// this can be a library API or an instruction as part of an ISA
int fma(int x, int y, int z) {
  return x + y * z;
}
```

The full transpiler from this tutorial can be found [in our repository](https://github.com/metalift/metalift/blob/main/tests/llvm/fma_dsl.py).

## Define the Target Language

Our first step is to define the semantics of the target language. Using Metalift, we define each construct in the target language as a _semantic function_. Such functions are just normal Python functions, except that its body is defined using the Metalift IR. For FMA [this looks like](https://github.com/metalift/metalift/blob/main/tests/llvm/fma_dsl.py#L47):

<!--phmdoctest-share-names-->
```python
from typing import List
from metalift.ir import fn_decl, fn_decl_recursive, choose, Synth
from metalift.ir import call, Lit, IntLit, Add, Call, Eq, Expr, Ite, Lit, Sub, TupleExpr
from metalift.ir import Int, Bool, Object

def targetLang():
  x = Int("x") # variables to be used in semantic function definition
  y = Int("y")
  z = Int("z")
  fma = fn_decl("fma",             # function name
               Int,             # return type
               x + y * z, # body of the function
               x, y, z)           # function inputs
  return [fma]
```

Here we first define three variables (lines 1-3), and use them to define a single semantic function, `fma`, which computes `x+y*z`. Notice that we are using Metalift's IR to define everything.

If our target language has more constructs, we would define more semantic functions.


## Search Space Description

After we have defined the target language, we next describe the space of programs our synthesizer should consider during transpilation. We do so by specifying a _grammar_, much like a programming language, except that we are restricted to using the semantic functions we have defined, along with any of the constructs from the Metalift base IR.

For our example, we want the synthesizer to consider transpiling the input code to programs that are either just an addition of the input variables, or the result of calling our `fma` instruction. We do it [as follows](https://github.com/metalift/metalift/blob/main/tests/llvm/fma_dsl.py#L37):

<!--phmdoctest-mark.skip-->
```python
# inputVars := one of the vars read in the input | 0
inputVars = choose(*ci.readVars, IntLit(0))
# var_or_add := inputVar + inputVar
var_or_add = inputVars + inputVars
# var_or_fma := one of the vars read | fma(var_or_add, var_or_add, var_or_add)
var_or_fma = choose(*ci.readVars, call("fma", Int, var_or_add, var_or_add, var_or_add))
```

A few things of note here:
- we construct the different options using Metalift's IR.
- we use Metalift's `Choose` construct to represent alternatives. for instance line 1 above says the non-terminal `inputVars` can be any of the variables that are read in the given code fragment, or the number `0`.
- similarly, line 3 says the `var_or_fma` non-terminal can be either one of the variables that are read in the input code, or a call to the `fma` instruction.

After that, we tell Metalift that all values should be computed using the grammar we defined.

<!--phmdoctest-share-names-->
```python
def grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]) -> Bool:
    ret_val = writes[0]
    var = choose(*reads, Int(0))
    added = var + var
    fma_call_object = call("fma", Int, added, added, added)
    var_or_fma = choose(*reads, fma_call_object)
    # all writes should be computed using the grammar above. I.e., written_var = var_or_fma + var_or_fma. and the return value must be equal to it
    return ret_val == var_or_fma + var_or_fma

```
We wrap this in a `Synth` AST node and return it afterwards.

Where do the read and written variables come from? They are provided by Metalift's code analyzer (more on this later), which is passed into our grammar function as the `CodeInfo` object, along with other info such as the input code's name. Our goal is to provide various types of analysis results to the developer so that they can programmatically generate the grammar for the transpiled code.


## Transpiler Flow

We can now finally put our transpiler together. First, we compile the input code to be transpiled into LLVM bitcode.

```cpp title="tests/llvm/fma_dsl.c"
int test(int base, int arg1, int base2, int arg2) {
  int a = 0;

  a = (base + base2) + arg1 * arg2;

  a = a + a;

  return a;
}
```

We do this using the [script provided by Metalift](https://github.com/metalift/metalift/blob/main/tests/compile-add-blocks). The script generates both the LLVM bitcode (.ll) file, along with a file containing loop information (.loops, which is empty since our input code does not contain any loops).

We pass these file names to Metalift's `analyze` function, which returns a number of results. The most important is the last one, which contains [information about the code to be transpiled](https://github.com/metalift/metalift/blob/main/metalift/analysis.py#L185). The code info is then used to generate our grammar as described above.

<!--phmdoctest-share-names-->
```python
from metalift.analysis_new import VariableTracker, analyze
from metalift.frontend.llvm import Driver

filename = "tests/llvm/fma_dsl.ll"
basename = "fma_dsl"

fnName = "test"
loopsFile = "tests/llvm/fma_dsl.loops"
cvcPath = "cvc5"

driver = Driver()
test = driver.analyze(
    llvm_filepath=filename,
    loops_filepath=loopsFile,
    fn_name=fnName,
    target_lang_fn=targetLang,
    inv_grammars=None,
    ps_grammar=grammar
)


base = Int("base")
arg1 = Int("arg1")
base2 = Int("base2")
arg2 = Int("arg2")
driver.add_var_objects([base, arg1, base2, arg2])

test(base, arg1, base2, arg2)
```

After we defined our target language and search space grammar, we call Metalift's `synthesize` function as described in our previous tutorial.

<!--phmdoctest-share-names-->
```python
from metalift.synthesize_auto import synthesize

driver.synthesize()
```

The synthesized code can then pass through our code generator to produce executable code.

<!--phmdoctest-share-names-->
```python
def codeGen(expr: Expr) -> str:
    def eval(expr: Expr) -> str:
        if isinstance(expr, Eq):
            return f"{expr.e1()} == {eval(expr.e2())}"
        if isinstance(expr, Add):
            return f"{eval(expr.args[0])} + {eval(expr.args[1])}"
        if isinstance(expr, Sub):
            return f"{eval(expr.args[0])} - {eval(expr.args[1])}"
        if isinstance(expr, Call):
            eval_args = []
            for a in expr.arguments():
                eval_args.append(eval(a))
            return f"{expr.name()}({', '.join(a for a in eval_args)})"
        if isinstance(expr, Lit):
            return f"{expr.val()}"
        if isinstance(expr, TupleExpr):
            return f"({', '.join(eval(a) for a in expr.args)})"
        if isinstance(expr, Ite):
            return f"{eval(expr.e1())} if {eval(expr.c())} else {eval(expr.e2())}"
        else:
            return "%s"%(expr)
    return eval(expr)

summary = test.codegen(codeGen)

print(summary)
```

```
fma(base + base2, 0 + arg1, arg2 + arg2) + fma(base + base2, base2 + 0, 0 + 0)
```
