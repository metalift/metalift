# same as fma.c but with multiplication written out as repeated addition
# only works if arg2 >= 0


def test(base1: int, arg1: int, base2: int, arg2: int) -> int:
    i = 0
    p = 0
    while i < arg2:
        p = p + arg1
        i = i + 1

    # p = arg1 * arg2 if arg2 >= 0
    a = (base1 + base2) + p
    a = a + a

    return a
