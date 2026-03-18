from typing import List


def conv1d(x: List[int], y: List[int]) -> int:
    return 0 if len(y) < 1 else x[0] * y[0] + conv1d(x[1:], y[1:])
