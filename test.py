import re


# regex to extract the code from the completions
def extract(s):
    return [
        x for x in re.findall(r"```(?:Python|python|assembly)?(.*?)```", s, re.DOTALL)
    ]


test_code = f"""
These loop invariants hold at the start and end of each loop iteration and they are used to prove the correctness of the loops in the `transformer_part1` function. The `invariant1` corresponds to the outer loop with the `timestep` variable while `invariant2` is for the inner loop with the `i` variable. In both invariants, we ensure that the loop variables are within their valid bounds and the computation of `attention` and `score` matches the expected values using the provided functions.
Based on the provided code, following are the loop invariants:

```python
def invariant1(token_position, head, head_size, key_cache_layer, q, attention, timestep):
    return timestep >= 0 and timestep <= token_position and attention == vec_scalar_div(integer_sqrt(head_size * 1), matrix_vec_mul(matrix_col_slice(matrix_row_slice(key_cache_layer, 0, timestep), head * head_size, head * head_size + head_size), vec_slice(q, head * head_size, head * head_size + head_size)))
```

This loop invariant asserts that at each timestep in the outer loop, the attention vector is equivalent to the vector produced by the scalar division of the integer square root of head_size by the vector multiplication of a sliced column of the key_cache_layer matrix and a sliced vector q.

```python
def invariant2(head, head_size, i, key_cache_layer, q, score, timestep, token_position):
    return i >= 0 and i <= head_size and score == reduce_sum(vec_elemwise_mul(vec_slice(q, head * head_size, head * head_size + head_size), matrix_col_slice(matrix_row_slice(key_cache_layer, timestep, timestep + 1), head * head_size, head * head_size + head_size)))
```

This loop invariant asserts that at each iteration in the inner loop, the score is equivalent to the sum of the element-wise multiplication of a sliced vector q and a sliced column of the key_cache_layer matrix.
"""

out = extract(test_code)
import pdb

pdb.set_trace()
print(out)
