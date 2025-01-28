# same as no_loop_matmul.cc


def test(a0: int, a1: int, b0: int, b1: int, x0: int, x1: int) -> int:
    p0 = a0 * x0 + b0 * x1
    p1 = a1 * x0 + b1 * x1
    if p0 < 0:
        p0 = -p0
    if p1 < 0:
        p1 = -p1
    return p0 + p1
