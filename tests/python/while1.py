# same as while1.c


def test(x: int) -> int:
    y: int = 0

    # inv: ite(y<=x, y<=x, y=0)
    while y < x:
        y = y + 1

    # ps: ite(y<=x, y=x, y=0)
    return y
