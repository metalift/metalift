# metalift input code

def input(n: int) -> int:
  sum: int = 0
  i: int = 0

  # invariant:
  # if n <= i and n <= 0: sum = 0
  # else: sum = my_sum(i)
  #
  while i < n:
    sum = sum + 1
    i = i + 1

  # postcondition:
  # if 0 <= n: sum = my_sum(n) and rv = sum
  # else: sum = 0 and rv = sum
  #
  return sum

#print('sum: %s' % input(20))
