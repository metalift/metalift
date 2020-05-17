# definitions of Map and Reduce using two auxiliary functions

from typing import Callable, List

# def do_map(l: List[int], f: Callable[[int], int], i: int) -> List[int]:
#   if i >= 0:
#     return do_map(l, f, i - 1) + [f(l[i])]  #out.append(f(l[i]))
#   else:
#     return []
#
# def Map(l: List[int], f: Callable[[int], int]) -> List[int]:
#   return do_map(l, f, len(l) - 1)
#
# # right fold
# def do_reduce(l: List[int], f: Callable[[int, int], int], v: int, i: int) -> int:
#   if i >= 0:
#     return do_reduce(l, f, f(l[i], v), i - 1)
#   else:
#     return v
#
# def Reduce(l: List[int], f: Callable[[int, int], int], init: int) -> int:
#   return do_reduce(l, f, init, len(l) - 1)
#
#
# def map_f(val: int) -> int:
#   return val * 2
#
# def reduce_f(v1: int, v2: int) -> int:
#   return v1 + v2



def mapper(data: List[int], f: Callable[[int], int  ]) -> List[int]:
  if len(data) == 0:
    return []
  else:
    return [f(data[0])] + mapper(data[1:], f)

def reducer(data: List[int], f: Callable[[int, int], int], init: int) -> int:
  if len(data) == 0:
    return init
  else:
    return f(data[0], reducer(data[1:], f, init))

# these functions are declared in the compiler
# def lambda_mapper(val: int) -> int:
#   return val * 2

# def lambda_reducer(v1: int, v2: int) -> int:
#   return v1 + v2


# test program
#
# l = [1,2,3,4]
# l2 = mapper(l, lambda_mapper)
# r = reducer(l2, lambda_reducer, 0)
# print(r)  # 20



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

