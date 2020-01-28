def my_sum(end: int) -> int :
  if end > 1:
    return 1 + my_sum(end - 1)
  else:
    return 1