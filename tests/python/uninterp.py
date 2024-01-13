# same as uninterp.c


def uninterp(i: int, j: int) -> int:
    return i


def test(i: int, j: int) -> int:
    return uninterp(i, i) + uninterp(j, j)
