# metalift input code
from typing import List


def input(l: List[int]) -> int:
  i: int = 0
  sum: int = 0

  # invariant:
  # def map_f(i: int) -> int:
  #   return i * 2
  #
  # def reduce_f(v1: int, v2: int) -> int:
  #   return v1 + v2
  #
  # i >= 0 and i <= len(l) and sum = Reduce(Map(l[0:i], map_f), reduce_f, 0)

  while i < len(l):
    sum = sum + (l[i] * 2)
    i = i + 1

  # postcondition:
  # sum = Reduce(Map(l, map_f), reduce_f, 0)
  #
  return sum


# print('sum: %s' % input([1,2,3,4]))
