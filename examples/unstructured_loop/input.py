# test code for break and continue
def input(n: int) -> int:
  sum: int = 0
  i: int = 0

  while i < n:
    i = i + 1
    if i == 2:
      break
    elif i == 3:
      continue
    i = i + 4

  return sum