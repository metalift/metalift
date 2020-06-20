# definitions of relational algebra

from typing import Callable, List

def Select(data: List[int], f: Callable[[int], bool]) -> List[int]:
  if len(data) == 0:
    return []
  elif f(data[0]):
    return [data[0]] + Select(data[1:], f)
  else:
    return Select(data[1:], f)


# test program
#
# l = [1,2,3,4]
# l2 = mapper(l, lambda_mapper)
# r = reducer(l2, lambda_reducer, 0)
# print(r)  # 20