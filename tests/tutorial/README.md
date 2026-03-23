# Writing a New Metalift Driver (RMSNorm Style)

This guide shows how to write a new driver file like `tests/tutorial/rmsnorm/rmsnorm_part1_driver.py`. A driver connects four things:

1. The source function to synthesize (`.cc` file + function name).
2. Preconditions over input variables.
3. DSL/IR function declarations the synthesizer can use.
4. Verification and axioms.

In practice, your script should:

- define helper DSL functions (if needed),
- define a precondition function,
- call `run_synthesis_for_cc(...)` in `__main__`.

## Instructions
More information can be found in `metalift/ir.py`, and you can always refer to our examples in driver files (files that end with `_driver.py`). For this tutorial, this README contains all the information you need.

### 1. Relevant IR Syntax
For this tutorial, you will only need integer and bool typed vars. You can instantiate an integer variable or a literal by the following:
```python
from metalift.ir import Int
int_x = Int("int_x") # variable
int_y = Int(1)   # int literal
```
You can perform arithmetic and comparison operations on these objects through python arithmetic such as `x + y`, `x - y`, `x == n`.


Similarly, you can instantiate a boolean variable or a literal by the following:

```python
from metalift.ir import Bool
bool_x = Bool("x")
bool_y = Bool(true)
```

or you can create boolean ir expressions by comparing two integers such as `int_x == int_y`.

Control flow syntax might also come in handy. In this case, condition is boolean type, `then_expr` and `else_expr` can be any expressions of the same type.

```python
ite(condition, then_expr, else_expr)
```

### 2. Adding preconditions
Define a function with the following signature, where `input_vars` is a dictionary mapping input variable names to `metalift.ir.Object` objects.The keys of this dictionary are the same as your C++ function argument names.

```python
def _your_test_func_preconditions(driver: Driver, input_vars: dict[str, Object]) -> None:
    input_var = input_vars["input"]
    driver.add_precondition(input_var == 1)
```

### 3. Declaring DSL functions the synthesizer may use

To add a DSL function, first, the most important two importants are
```python
from metalift.ir import call, fn_decl_recursive
```

Follow the steps below
- Create a string name (`MY_OP = "my_op"`).
- Make input variables as described above.
- Write a typed `call_*` wrapper with `call`. This function takes in the following:
    1. `fn_name`: str,
    2. `return_type`: IR type (`Int` or `Bool`),
    3. `*input_variables`: Input IR variables you made.
- Write a body expressed as an IR expression.
- Define your function using `fn_decl_recursive`, which takes in the following:
    1. `fn_name`: str,
    2. `return_type`: IR type (`Int` or `Bool`),
    3. `body_expr`: The expression you defined above.
    4. `*input_variables`: Input IR variables you made.

### 5. Create __name__ == "__main__"
Call `run_synthesis_for_cc`. You only need to pass in the following arguments:
1. `cc_path`: The path to your C++ code.
2. `fn_name`: Name of the source function you want to translate in your C++ file.
3. `precondition_fn`: As defined above.
4. `llm_model`: `LLMModel.BEDROCK` for this tutorial.
5. `dsl_fns`: A list of function declarations defined above.
6. `verification_method`: `VerificationMetho.SMT` for this tutorial

## Running the driver

From repo root:

```bash
python {my_driver.py}
```

If synthesis succeeds, generated artifacts/logs are written under `synthesisLogs/verify_{fn_name}.smt` where `fn_name` is the argument you pass to `run_synthesis_for_cc`.
