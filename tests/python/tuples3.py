# same as tuples3.cc


def test(x: int, y: int) -> int:
    u = (x, x)
    v = (y, y)
    z = u[0] + u[1] + v[0] + v[1]
    return z
