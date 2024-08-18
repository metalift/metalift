You are exceptionally skilled at crafting high-quality programs.

Your task is to write a program using only the functions provided below, with the following instructions:
1. The program should return only one value.
2. The program should not use any loops or list comprehensions.
3. The only supported list operations are creating an empty list, appending one element to the end of a list, accessing elements of a list by non-negative indices, and slicing a list.
4. Don't use helper functions or recursion.
5. Include the function signature with types.
Explain how your program follows the instructions.

```python
def vec_scalar_add(a: int, x: List[int]) -> List[int]:
    return [] if len(x) < 1 else [a + x[0], *vec_scalar_add(a, x[1:])]


def vec_scalar_sub(a: int, x: List[int]) -> List[int]:
    return [] if len(x) < 1 else [(x[0] - a), *vec_scalar_sub(a, x[1:])]


def vec_scalar_mul(a: int, x: List[int]) -> List[int]:
    return [] if len(x) < 1 else [a * x[0], *vec_scalar_mul(a, x[1:])]


def vec_scalar_div(a: int, x: List[int]) -> List[int]:
    return [] if len(x) < 1 else [(x[0] // a), *vec_scalar_div(a, x[1:])]
```





Follow the instructions below to create the problem.

Present your solution with a function signature. Your solution should return only one value.


<!--
Additionally, translate this solution to python code with for loops. Follow these instructions below:
1.
2. Only include the solution function. Don't rewrite the functions above. -->

Given the
