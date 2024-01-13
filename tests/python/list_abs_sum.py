# same as list_abs_sum.cc

from typing import List


def test(lst: List[int]) -> int:
    i: int = 0
    sum: int = 0
    while i < len(lst):
        curr_el: int = lst[i]
        if curr_el < 0:
            sum = sum - curr_el
        else:
            sum = sum + curr_el
        i = i + 1
    return sum
