---
sidebar_position: 1
---

# LLMs for Verified Lifting

Large Language Models (LLMs) have emerged as a promising approach for tackling complex programming tasks, including code generation, repair, and testing. However, generating reliable code with formal correctness guarantees with LLMs remains challenging. To leverage LLMs for building verified lifting compilers, we must address two key constraints:
generalization to new DSLs and providing correctness guarantees for the generated code. In this tutorial, we illustrate how to use LLMs for building a verified lifting- based compiler (LLMLift).

LLMLIFT, takes inspiration from the core technique of VL, which involves translating the source program to a higher-level intermediate representation (IR) that describes the semantics of the DSL operators. Once the synthesized code is verified, it is then translated to the concrete syntax of the DSL using rewrite rules. We leverage the reasoning capabilities of LLMs to translate code from context to an IR. We instruct the model via a prompt to generate code using the operators of the DSL, with Python serving as the IR to encode the semantics of these operators. Python’s significant representation in the training datasets of LLMs makes it a suitable choice for this purpose. In addition to generating the DSL program, we also prompt the model to generate a proof of correctness for the program.

In this tutorial, our goal is to build a simple transpiler for translating a sequential C++ to tensor-processing frameworks (such as PyTorch, Tensorflow, NumPy).

**Source C++ Code (S):**

```cpp
vector<vector<int>> test(vector<vector<int>> b, vector<vector<int>> a) {
    vector<vector<int>> out;
    for (int row = 0; row < b.size(); row++) {
        vector<int> row_vec;
        for (int col = 0; col < b[0].size(); col++) {
            int pixel = b[row][col] + a[row][col] - 255;
            row_vec.push_back(pixel);
        }
        out.push_back(row_vec);
    }
    return out;
}
```

This sequential source program performs the linear burn blending operation in image editing. The given source program takes as input two images (represented as 2D vectors) and processes each pixel from both the images by first adding them and then subtracting by integer 255.

We need to compile the source code to LLVM bytecode using the [script provided by Metalift](https://github.com/metalift/metalift/blob/main/metalift/utils/llvm/compile-add-blocks). The script generates both the LLVM bitcode (.ll) file by calling the Clang compiler, along with a file containing loop information.

Similar to the previous tutorials, the next step is to define the target language. We will define the semantics of the tensor operators such as `matrix_add` and `matrix_scalar_sub`.

<!--phmdoctest-mark.skip-->
```python
def elemwise_body(
    left: Union[mlList[Int], Matrix[Int], Tensor3D[Int]],
    right: Union[mlList[Int], Matrix[Int], Tensor3D[Int]],
    compute_fn: Callable[[Int, Int], Int],
    vec_fn_name: str,
    matrix_fn_name: str,
    tensor3d_fn_name: str,
) -> Union[mlList[Int], Matrix[Int]]:
    cur = call(vec_fn_name, mlList[Int], left[0], right[0])
    recursed = call(matrix_fn_name, Matrix[Int], left[1:], right[1:])
    general_answer = recursed.prepend(cur)
    return ite(
        or_objects(left.len() < 1, left.len() != right.len()),
        Matrix.empty(Int),
        general_answer,
    )

matrix_elemwise_add = fn_decl_recursive(
    MATRIX_ELEMWISE_ADD,
    Matrix[Int],
    elemwise_body(
        left=matrix_x,
        right=matrix_y,
        compute_fn=lambda int_x, int_y: int_x + int_y,
        vec_fn_name=VEC_ELEMWISE_ADD,
        matrix_fn_name=MATRIX_ELEMWISE_ADD,
        tensor3d_fn_name=TENSOR3D_ELEMWISE_ADD,
    ),
    matrix_x,
    matrix_y,
)
```

<!--phmdoctest-mark.skip-->
```python
def scalar_body(
    scalar: Int,
    vec_or_matrix: Union[mlList[Int], Matrix[Int]],
    compute_fn: Callable[[Int, Int], Int],
    vec_fn_name: str,
    matrix_fn_name: str,
) -> Union[mlList[Int], Matrix[Int]]:

    cur = call(vec_fn_name, mlList[Int], scalar, vec_or_matrix[0])
    recursed = call(matrix_fn_name, Matrix[Int], scalar, vec_or_matrix[1:])
    general_answer = recursed.prepend(cur)
    return ite(
        or_objects(vec_or_matrix.len() < 1), Matrix.empty(Int), general_answer
    )

matrix_scalar_sub = fn_decl_recursive(
    MATRIX_SCALAR_SUB,
    Matrix[Int],
    scalar_body(
        scalar=a,
        vec_or_matrix=matrix_x,
        compute_fn=lambda scalar, int_x: int_x - scalar,
        vec_fn_name=VEC_SCALAR_SUB,
        matrix_fn_name=MATRIX_SCALAR_SUB,
    ),
    a,
    matrix_x,
)
```

## Synthesis

In the previous tutorials, we asked the user to define the search space for loop invairants and program summaries. With LLMLift, we do not require the users to provide any of these search space descriptions. Instead, we leverage the few-shot reasoning capability by providing the models with the semantics of operators from the target language using an IR. By exposing the LLMs to these semantics, we enable them to use their reasoning capabilities over code to generate both the PS and invariants in the IR.

As before, write your own driver file. This includes:
1. Supplying some information about the loops in your programs, if any, to help LLMLift generate a template for synthesizing invariants. [Here](https://github.com/metalift/metalift/blob/main/benchmarks/blend/driver/multiply_blend_8_driver.py#L22-L36) is an example. We are working to automate this step!
2. Specify the output variable, as the example [here](https://github.com/metalift/metalift/blob/main/benchmarks/blend/driver/multiply_blend_8_driver.py#L37).
3. You can select your favorite LLM model by setting the llm_model argument to ```run_llm_synthesis_algorithm```. Currently, we support Claude, GPT, and Gemini. You can use any of these three models by setting their corresponding API keys (OPENAI_API_KEY, CLAUDE_API_KEY, GEMINI_API_KEY) in a .env file.
4. For initial testing, we recommend using bounded verification, which can be set through the verification_method argument. You can either set it to VerificationMethod.ROSETTE or VerificationMethod.SMT. Full verification (VerificationMethod.SMT) requires additional axioms for the SMT solver to reason over your custom DSLs. You can see one example of the axiom [here](https://github.com/metalift/metalift/blob/main/metalift/utils/tenspiler/axioms.py#L141-L149). For more details on axioms on verified lifting, you can refer to the original MetaLift [paper](https://drops.dagstuhl.de/storage/00lipics/lipics-vol263-ecoop2023/LIPIcs.ECOOP.2023.38/LIPIcs.ECOOP.2023.38.pdf).

<!--phmdoctest-mark.skip-->
```python
 run_llm_synthesis_algorithm(
        driver=driver,
        loop_info=loop_info,
        output_var=output_var,
        source_code=input_code,
        benchmark_name="lighten_blend",
        llm_model=LLMModel.GPT,
        dsl_fns=TENSPILER_FNS,
        verification_method=VerificationMethod.ROSETTE,
    )
```

The model generates the following PS and invariant for the given source code, representing it as a combination of DSL operators:
```matrix_scalar_sub(255, matrix_elemwise_add(b, a))```

<!--phmdoctest-mark.skip-->
```python
def invariant_outer(row, col, b, a, out):
    return row >= 0 and row <= len(b) and out == matrix_scalar_sub(255, matrix_add(b[:i], a[:i]))
```

Our full paper presented at NeurIPS can be found [here](https://openreview.net/forum?id=spwE9sLrfg).
