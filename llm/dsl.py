from typing import List


def conv1d(x: List[int], y: List[int], W: int, W_f: int) -> int:
    return (
        []
        if W < 1
        else [reduce_sum(vec_elemwise_mul(x[:W_f], y)), *conv1d(x[1:], y, (W - 1), W_f)]
    )
