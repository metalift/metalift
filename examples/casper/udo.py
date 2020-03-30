# definitions of Map and Reduce using two auxiliary functions

from typing import Callable, List

def Map(l: List[int], f: Callable[[int], int]) -> List[int]:
  return do_map(l, f, len(l) - 1)

def do_map(l: List[int], f: Callable[[int], int], i: int) -> List[int]:
  out: List[int]
  if i >= 0:
    out = do_map(l, f, i - 1)
    out.append(f(l[i]))
  else:
    out = []
  return out

def Reduce(l: List[int], f: Callable[[int, int], int], init: int) -> int:
  return do_reduce(l, f, init, len(l) - 1)

# right fold
def do_reduce(l: List[int], f: Callable[[int, int], int], v: int, i: int) -> int:
  if i >= 0:
    r: int
    r = f(l[i], v)
    return do_reduce(l, f, r, i - 1)
  else:
    return v


# test program
#
# def map_f(i: int) -> int:
#   return i + 10
#
# def reduce_f(v1: int, v2: int) -> int:
#   return v1 + v2
#
# l = [1,2,3,4]
# l2 = Map(l, map_f)
# print(l2)
# r = Reduce(l2, reduce_f, 0)
# print(r)  # 50
