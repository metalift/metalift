# target 'language' to lift to
def my_sum(end: int) -> int:
  if end > 0:
    return 1 + my_sum(end - 1)
  else:
    return 0
