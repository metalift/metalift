# same as while3.c

def test(input_arg: int) -> int:
    x: int = 0
    y: int = 1
    while y < input_arg:
        x = x + y
        y = y + 1
    return x