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

The full transpiler from this tutorial can be found [in our repository](https://github.com/metalift/metalift/blob/main/tests/fma_dsl.py).

## Define the Target Language

Our first step is to define the semantics of the target language. Using Metalift, we define each construct in the target language as a _semantic function_. Such functions are just normal Python functions, except that its body is defined using the Metalift IR. For FMA [this looks like](https://github.com/metalift/metalift/blob/main/tests/fma_dsl.py#L47):

<!--phmdoctest-share-names-->
```python
from metalift.ir import Var, FnDecl, FnDeclNonRecursive, Choose, Synth
from metalift.ir import Add, Mul, Eq, Call, Lit, IntLit
from metalift.ir import Int

def targetLang():
  x = Var("x", Int()) # variables to be used in semantic function definition
  y = Var("y", Int())
  z = Var("z", Int())
  fma = FnDeclNonRecursive("fma",             # function name
                           Int(),             # return type
                           Add(x, Mul(y, z)), # body of the function
                           x, y, z)           # function inputs
  return [fma]
```

Here we first define three variables (lines 1-3), and use them to define a single semantic function, `fma`, which computes `x+y*z`. Notice that we are using Metalift's IR to define everything.

If our target language has more constructs, we would define more semantic functions. 


## Search Space Description

After we have defined the target language, we next describe the space of programs our synthesizer should consider during transpilation. We do so by specifying a _grammar_, much like a programming language, except that we are restricted to using the semantic functions we have defined, along with any of the constructs from the Metalift base IR.

For our example, we want the synthesizer to consider transpiling the input code to programs that are either just an addition of the input variables, or the result of calling our `fma` instruction. We do it [as follows](https://github.com/metalift/metalift/blob/main/tests/fma_dsl.py#L37):

<!--phmdoctest-mark.skip-->
```python
# inputVars := one of the vars read in the input | 0
inputVars = Choose(*ci.readVars, IntLit(0))
# var_or_add := inputVar + inputVar
var_or_add = Add(inputVars, inputVars)
# var_or_fma := one of the vars read | fma(var_or_add, var_or_add, var_or_add)
var_or_fma = Choose(*ci.readVars, Call("fma", Int(), var_or_add, var_or_add, var_or_add))
```

A few things of note here:
- we construct the different options using Metalift's IR.
- we use Metalift's `Choose` construct to represent alternatives. for instance line 1 above says the non-terminal `inputVars` can be any of the variables that are read in the given code fragment, or the number `0`.
- similarly, line 3 says the `var_or_fma` non-terminal can be either one of the variables that are read in the input code, or a call to the `fma` instruction.

After that, we tell Metalift that all values should be computed using the grammar we defined.

<!--phmdoctest-share-names-->
```python
def grammar(ci):
  name = ci.name

  inputVars = Choose(*ci.readVars, IntLit(0))
  var_or_add = Add(inputVars, inputVars)
  var_or_fma = Choose(
    *ci.readVars, Call("fma", Int(), var_or_add, var_or_add, var_or_add)
  )
  
  rv = ci.modifiedVars[0]
  # all writes should be computed using the grammar above. I.e., written_var = var_or_fma + var_or_fma 
  summary = Eq(rv, Add(var_or_fma, var_or_fma))

  return Synth(name,                            # name of the function we are transpiling
               summary,                         # grammar defined above
               *ci.modifiedVars, *ci.readVars)  # list of input and output variables

```
We wrap this in a `Synth` AST node and return it afterwards.

Where do the read and written variables come from? They are provided by Metalift's code analyzer (more on this later), which is passed into our grammar function as the `CodeInfo` object, along with other info such as the input code's name. Our goal is to provide various types of analysis results to the developer so that they can programmatically generate the grammar for the transpiled code. 


## Transpiler Flow

We can now finally put our transpiler together. First, we compile the input code to be transpiled into LLVM bitcode.

```cpp title="tests/fma_dsl.c"
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
from metalift.analysis import analyze

filename = "tests/fma_dsl.ll"
basename = "fma_dsl"

fnName = "test"
loopsFile = "tests/fma_dsl.loops"
cvcPath = "cvc5"

(vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile)

print("====== grammar")
invAndPs = [grammar(ci) for ci in loopAndPsInfo]

lang = targetLang()
```

After we defined our target language and search space grammar, we call Metalift's `synthesize` function as described in our previous tutorial.

<!--phmdoctest-share-names-->
```python
from metalift.synthesize_auto import synthesize

candidates = synthesize(
  basename, lang, vars, invAndPs, preds, vc, loopAndPsInfo, cvcPath
)
```

The synthesized code can then pass through our code generator to produce executable code.

<!--phmdoctest-share-names-->
```python
def codeGen(summary: FnDecl):
  expr = summary.body() 
  def eval(expr):
    if isinstance(expr, Eq):
      return f"{expr.e1()} = {eval(expr.e2())}"
    elif isinstance(expr, Add):
      return f"{eval(expr.args[0])} + {eval(expr.args[1])}"
    elif isinstance(expr, Call):
      eval_args = []
      for a in expr.arguments():
        eval_args.append(eval(a))
      return f"{expr.name()}({', '.join(eval_args)})"
    elif isinstance(expr, Lit):
      return str(expr.val())
    else:
      return str(expr)
  return eval(expr)

summary = codeGen(candidates[0])

print(summary)
```

```
i18 = fma(arg2 + arg, 0 + 0, arg3 + arg) + fma(arg + arg2, arg3 + arg3, 0 + arg1)
```
