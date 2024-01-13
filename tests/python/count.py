# same as Count.cc

from typing import List


def test(in_lst: List[int]) -> int:
    count: int = 0
    i: int = 0
    while i < len(in_lst):
        count = count + 1
        i = i + 1
    return count
