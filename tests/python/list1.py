# same as list1.cc

from typing import List


def test(in_lst: List[int]) -> List[int]:
    out_lst: List[int] = []
    i: int = 0
    while i < len(in_lst):
        out_lst.append(in_lst[i])
        i = i + 1
    return out_lst
