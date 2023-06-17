---
sidebar_position: 1
---

# Building a transpiler for hardware accelerator

Hardware accelerators have proven to be very effective in optimizing computationally expensive DNN workflows. [Gemmini](https://github.com/ucb-bar/gemmini) is an open-source framework for building custom DNN accelerators. It allows developers to generate accelerators and customize them end-to-end, from architectural templates (such as spatial arrays and scratchpads) to programming support (including ONNX format and low-level C++ APIs) to system support (such as microcontrollers and server-class CPUs).

At present, Gemmini offers two front-ends for running DNN workloads: high-level push-button support for executing workloads from ONNX files and hand-tuned C/C++ APIs of different popular kernels that perform operations such as matrix multiplication, convolutions, and max-pools. 


Now, suppose we have the following source code:

```cpp
vector<int> program(vector<int> data){
    vector<int> result;
    for (int i = 0; i < data.size() - 1; i++)
        result.push_back(data[i] + data[i + 1]);
    return result
}
```

Readers familiar with primitives for tensor accelerators may recognize this as a convolution, but this is not explicit in the code. With current programming model support, developers would need to manually convert this code to one of the supported front-end of Gemmini. In this tutorial, we demonstrate how to build a transpiler using Metalift that can convert this code to the C/C++ APIs of Gemmini.

## Define the Target Language
The first step in using Metalift to build this transpiler is to define the semantics of the opertors in Gemmini's ISA (convolution, matrix multiplication, max-pool) using Metalift's IR. For this tutorial, we will just need the following definition of 1D convolution operation. 

```python
from metalift.ir import Var, FnDecl, FnDeclRecursive, Choose, Synth
from metalift.ir import Add, Mul, Eq, Call, Lit, IntLit, Ite
from metalift.ir import Int, Bool, ListT, And, Or, Not, Ge, Gt, Le, Lt, Sub

def ml_list_get(lst, i):
    return Call("list_get", Int(), lst, i) #returns lst[i]

def ml_list_tail(lst, i):
    return Call("list_tail", ListT(Int()), lst, i) #returns list[1:]

def ml_list_prepend(e, lst):
    return Call("list_prepend", ListT(Int()), e, lst) #returns e + lst

def ml_list_length(lst):
    return Call("list_length", Int(), lst) #returns len(lst)

def ml_list_empty():
    return Call("list_empty", ListT(Int())) #returns []

def ml_list_take(lst, i):
    return Call("list_take", ListT(Int()), lst, i) #returns lst[:i]

def ml_list_head(lst):
    return ml_list_get(lst, IntLit(0)) #return lst[0]

def targetLang():
    x = Var("x", ListT(Int()))
    y = Var("y", ListT(Int()))
    def dotprod_body(x, y):
        kernel_size = ml_list_length(y)
        cur_prod = Mul(ml_list_get(x, IntLit(0)), ml_list_head(y, IntLit(0)))
        x_rest = ml_list_tail(x, IntLit(1))
        y_rest = ml_list_tail(y, IntLit(1))
        recursed = Call("dotprod", Int(),x_rest, y_rest)
        return Ite(Lt(kernel_size, IntLit(2)), cur_prod, Add(cur_prod, recursed))
    dotprod = FnDeclRecursive("dotprod", Int(), dotprod_body(x, y), x, y)

    def conv1d1x2_body(vec, kernel):
        vec_size = ml_list_length(x)
        kernel_size = IntLit(2)
        cur_prod = Call("dotprod", Int(), vec, kernel)
        vec_rest = ml_list_tail(vec, IntLit(1))
        recursed = Call("conv1d", ListT(Int()),vec_rest, kernel)
        general_answer = ml_list_prepend(cur_prod, recursed)
        return Ite(Lt(vec_size, kernel_size), ml_list_empty(), general_answer)
    conv1d1x2 = FnDeclRecursive("conv1d", ListT(Int()), conv1d1x2_body(x, y), x, y)
    return [dotprod, conv1d1x2]
```

Metalift provides implementations of common list functions such as ```length, tail, take, prepend``` and can be accessed using the ```Call``` operator as shown in line 2. The targetLang defines ```conv1d``` as a function that takes as input ```vector``` and ```kernel```. At each step, it recursively calculates the dot product between the values in the window and the kernel. The pseudo code of the above implementation is as follows:

```python
def dotproduct(vec, kernel):
    if len(kernel) < 2:
        return vec[0]*kernel[0]
    else:
        return vec[0]*kernel[0] + dotproduct(vec[1:],kernel)
def conv1d1x2(vec,kernel):
    if len(vec) < len(kernel):
        return []
    else:
        return dotproduct(vec, kernel) + conv1d1x2(vec[1:],kernel)
```

## Search Space Description

After defining the target language, we will define the search space which describes the space of possible programs the synthesizer will explore during the search process. The search space describes the possible ways that our output variables (i.e., values that are returned to the user in our source code) can be computed using our target language. Metalift internally translates the source code to a Hoare-style verification condition (VC). As the given source code involves loops, an additional predicate called the [loop invariant](https://en.wikipedia.org/wiki/Loop_invariant) is required to prove the equivalence between source code and the translated code. Similar to how we define the search space for our output variables, we will define the search for the loop invariants as well. 

Metalift IR provides ```Choose``` construct to define the search space. For our example, one possible search space is given below:


```python
# defining the possible values for the kernel 
unknown_const = Choose(*[IntLit(coef) for coef in range(-3, 3 + 1)])
kernel = reduce(lambda acc, _cur: ml_list_prepend(unknown_const, acc), range(2), ml_list_empty()) 

# invariant grammar
def inv_grammar(ci: CodeInfo):
    an_input = Choose(*ci.readVars)
    an_output_i32 = ci.modifiedVars[1] #loop counter `i` of source code
    an_output_list = ci.modifiedVars[0] #output variable `result` of the source 
                                        #code

    valid = Gt(ml_list_length(an_input), IntLit(1)) 
    # This enforces the pre-loop invariant condition, that the looping index
    # is always at least 0.
    preloop = Ge(an_output_i32, IntLit(0))
    
    # This enforces the post-loop invariant condition, that the looping
    # index is at most the last index of the list.
    postloop = Le(an_output_i32, Sub(ml_list_length(an_input), IntLit(1)))
            
    # This enforces the inductive property, that if the output so far is
    # the convolution of the input and kernel so far, then it will continue
    # being the convolution of the input and kernel.
    induction = Eq(an_output_list,Call("conv1d", ListT(Int()),ml_list_take(an_input, Add(an_output_i32, IntLit(1)))),kernel)
    summary = Implies(valid, And(preloop, And(postloop, induction)))

    return Synth(name, summary, *ci.modifiedVars, *ci.readVars)
    '''
        BNF representation of the above code
        summary := And(i >= 0, i <= len(input) - 1, induction)
        induction := result = conv1d1x2(input[:i+1], kernel)
        kernel := [val,val]
        val := -3 | -2 | -1 | 0 | 1 | 2 | 3
    '''
def post_condition_grammr(ci: CodeInfo):
    # We require that, when the input and kernel lists are the same size,
    # that the output list is  1D convolution of the kernel over the input .
    an_input = ci.readVars[0]
    an_output = Choose(*ci.modifiedVars)
    x = ci.readVars[0]
    valid = Gt(ml_list_length(x), IntLit(1))
    ans = Call("conv2d", ListT(Int()), an_input, kernel)
    check_ans = Eq(ans, an_output)
    summary = Implies(valid, check_ans)
    return Synth(name, summary, *ci.modifiedVars, *ci.readVars)

    '''
        BNF representation of the above code
        summary = result = conv1d1x2(input, kernel)
        kernel := [val,val]
        val := -3 | -2 | -1 | 0 | 1 | 2 | 3
    '''
```

The ```CodeInfo``` object consists of all the variables that are modified in the source code ```i, result``` and all the variables that are input to the source code ```data```. The structure of the grammar can be controlled programmatically. For example, one of the strategies we can use for the example above is to incrementally increase the size of the kernel.


## Transpiler flow
Once the target operators semantics and the search space description is defined, we can build the transpiler now. First, we need to compiler the source code to LLVM bytecode using the [script provided by Metalift].(https://github.com/starptr/metalift/blob/oscar/main/tests/compile-add-blocks). The script generates both the LLVM bitcode (.ll) file by calling the Clang compiler, along with a file containing loop information.

```python
from metalift.analysis import CodeInfo, analyze
def runner(basename):
    filename = f"tests/{basename}.ll"
    fnName = "test"
    loopsFile = f"tests/{basename}.loops"
    cvcPath = "cvc5"

    (vars, invAndPs, preds, vc, loopAndPsInfo) = analyze(filename, fnName, loopsFile, log=False)

    invAndPs = [grammar(ci, kernel_size) for ci in loopAndPsInfo]
    lang = targetLang()
```

We pass these file names to Metalift's `analyze` function, which returns a number of results. The most important is the last one, which contains information about the code to be transpiled. The ```codeInfo``` is then used to generate our grammar as described above.

After we defined our target language and search space grammar, we call Metalift's `synthesize` function to search for the program and the ivariants which can prove the equivalence between the source code and the generated code in the target language.
```python
from metalift.synthesize_auto import synthesize
candidates = synthesize("conv1d", lang, vars, invAndPs, preds, vc, loopAndPsInfo, cvcPath, listBound=3, noVerify=True)
print(f"Synthesis took {end_time - start_time} seconds")
```

The synthesis phase returns the following solution:

```result = conv1d(data, kernel = [1,1])```

which means that Metalift's synthesizer found the output value computed by our source code can also be computed by calling the `conv1d` function defined in our target language when passed with the appropriate arguments. 

The synthesized code can then pass through our [code generator](https://github.com/starptr/metalift/blob/6267e705841776767a16999cd32c14829b277114/tests/conv1d.py#L213) to produce executable gemmini code. The generated code can be run on gemmini by following the instructions [here](https://github.com/ucb-bar/gemmini/tree/dev). The full example can be found [here](https://github.com/starptr/metalift/blob/6267e705841776767a16999cd32c14829b277114/tests/conv1d.py). 
