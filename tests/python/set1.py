# same as set1.c

from typing import Set


def test(s: Set[int], add: int, value: int) -> Set[int]:
    if add == 1:
        s.add(value)
    else:
        s.remove(value)
    return s
