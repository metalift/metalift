# test code for nested loops
def input(n: int) -> int:
  i: int = 0
  j: int = 0

  while i < n:
    i = i + 1
    while j < n:
      j = j + 2
      if i == 3:
        break
      elif i == 4:
        continue
      j = j + 5
    i = i + 6

  return i