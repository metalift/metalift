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
The first step in using Metalift to build this transpiler is to define the semantics of the opertors in Gemmini's ISA (convolution, matrix multiplication, max-pool) using Metalift's IR. For this tutorial, we will just need the following definition of 1D convolution operation using the mlList IR provided.

<!--phmdoctest-share-names-->
```python
from metalift.ir import fn_decl, fn_decl_recursive, choose, Synth
from metalift.ir import call, Lit, IntLit, ite
from metalift.ir import Int, Bool, List as mlList

def targetLang():
    x = mlList(Int, "x")
    y = mlList(Int, "y")
    def dotprod_body(x, y):
        kernel_size = len(y)
        cur_prod = x[0] * y[0]
        x_rest = x[1:]
        y_rest = y[1:]
        recursed = call("dotprod", Int, x_rest, y_rest)
        return ite(kernel_size < 2, cur_prod, cur_prod + recursed)
    dotprod = fn_decl_recursive("dotprod", Int, dotprod_body(x, y), x, y)

    def conv1d1x2_body(vec, kernel):
        vec_size = len(x)
        kernel_size = IntLit(2)
        cur_prod = call("dotprod", Int, vec, kernel)
        vec_rest = vec[1:]
        recursed = call("conv1d", mlList[Int],vec_rest, kernel)
        general_answer = cur_prod.append(recursed)
        return ite(vec_size < kernel_size, mlList.empty(Int), general_answer)
    conv1d1x2 = fn_decl_recursive("conv1d", mlList[Int], conv1d1x2_body(x, y), x, y)
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

<!--phmdoctest-mark.skip-->
```python
# defining the possible values for the kernel
unknown_const = choose(*[IntLit(coef) for coef in range(-3, 3 + 1)])
kernel = reduce(lambda acc, _cur: unknown_const.append(acc), range(2), mlList.empty(Int))

# invariant grammar
def inv_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]):
    an_input = reads[0]
    an_output_i32 = writes[1] #loop counter `i` of source code
    an_output_list = writes[0] #output variable `result` of the source
                                        #code

    valid = len(an_input) > 1
    # This enforces the pre-loop invariant condition, that the looping index
    # is always at least 0.
    preloop = an_output_i32 >= 0

    # This enforces the post-loop invariant condition, that the looping
    # index is at most the last index of the list.
    postloop = an_output_i32 <= len(an_input) - 1

    # This enforces the inductive property, that if the output so far is
    # the convolution of the input and kernel so far, then it will continue
    # being the convolution of the input and kernel.
    induction = an_output_list == call("conv1d", mlList[Int], an_input[:an_output_i32+1],kernel)
    summary = implies(valid, preloop and postloop and induction)

    return summary
    '''
        BNF representation of the above code
        summary := And(i >= 0, i <= len(input) - 1, induction)
        induction := result = conv1d1x2(input[:i+1], kernel)
        kernel := [val,val]
        val := -3 | -2 | -1 | 0 | 1 | 2 | 3
    '''
def post_condition_grammar(writes: List[Object], reads: List[Object], in_scope: List[Object]):
    # We require that, when the input and kernel lists are the same size,
    # that the output list is  1D convolution of the kernel over the input .
    an_output = writes[0]
    an_input = reads[0]
    x = reads[0]

    valid = len(x) > 1
    ans = call("conv2d", mlList[Int], an_input, kernel)
    check_ans = ans == an_output
    summary = implies(valid, check_ans)
    return summary

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

<!--phmdoctest-mark.skip-->
```python
from metalift.analysis import CodeInfo, analyze

filename = "tests/llvm/conv1d.ll"
fnName = "test"
loopsFile = "tests/llvm/conv1d.loops"
cvcPath = "cvc5"

driver = Driver()
test = driver.analyze(
    llvm_filepath=filename,
    loops_filepath=loopsFile,
    fn_name=fnName,
    target_lang_fn=targetLang,
    inv_grammars=defaultdict(lambda: inv_grammar),
    ps_grammar=post_condition_grammar
)
```

We pass these file names to Metalift's `analyze` function, which returns a number of results. The most important is the last one, which contains information about the code to be transpiled. The ```codeInfo``` is then used to generate our grammar as described above.

After we defined our target language and search space grammar, we call Metalift's `synthesize` function to search for the program and the ivariants which can prove the equivalence between the source code and the generated code in the target language.
<!--phmdoctest-mark.skip-->
```python
from metalift.synthesize_auto import synthesize
data_var = mlList(Int, "data")
driver.add_var_object(data_var)
test(data_var)

driver.synthesize()
print(f"Synthesis took {end_time - start_time} seconds")
```

The synthesis phase returns the following solution:

```result = conv1d(data, kernel = [1,1])```

which means that Metalift's synthesizer found the output value computed by our source code can also be computed by calling the `conv1d` function defined in our target language when passed with the appropriate arguments.

The synthesized code can then pass through our [code generator](https://github.com/starptr/metalift/blob/6267e705841776767a16999cd32c14829b277114/tests/conv1d.py#L213) to produce executable gemmini code. The generated code can be run on gemmini by following the instructions [here](https://github.com/ucb-bar/gemmini/tree/dev). The full example can be found [here](https://github.com/starptr/metalift/blob/6267e705841776767a16999cd32c14829b277114/tests/conv1d.py).
