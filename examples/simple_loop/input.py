# metalift input code

def input(n: int) -> int:
  sum: int = 0
  i: int = 0

  # invariant:
  # if i <= n: i >= 0 and sum = my_sum(i)
  # else: sum = 0
  #
  while i < n:
    sum = sum + 1
    i = i + 1

  # postcondition:
  # if i <= n: sum = my_sum(n)
  # else: sum = 0
  #
  return sum

#print('sum: %s' % input(20))
