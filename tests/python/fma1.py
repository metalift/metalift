# same as fma.c


def test(base1: int, arg1: int, base2: int, arg2: int) -> int:
    a = (base1 + base2) + arg1 * arg2
    a = a + a

    return a
