# metalift input code
from typing import List

# the goal is to rewrite the body of this function into one that only uses
# the operators defined in udo.py (i.e., map and reduce)
def input(l: List[int]) -> List[int]:
  i: int = 0
  out: List[int] = []

  # invariant:
  # def select_p(i: int) -> bool:
  #   return i == 2
  #
  # i >= 0 and i <= len(l) and out = Select(l[0:i], select_p)

  while i < len(l):
    if l[i] == 2:
      out = out + [l[i]]
    i = i + 1

  # postcondition:
  # out = Select(l, select_p)
  #
  return out


#print('select: %s' % input([1,2,3,2,4,2]))
