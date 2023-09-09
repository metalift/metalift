# same as while4.c

def test() -> int:
    x: int = 0
    y: int = 1
    while y < 3:
        x = x + y
        y = y + 1
    return x