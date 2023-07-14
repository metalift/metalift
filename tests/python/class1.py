# similar to struct1.c

class Test:
    field1: int
    field2: int

def test(f1: int, f2: int) -> int:
    t = Test()
    t.field1 = f1
    t.field2 = f2
    return t.field1 + t.field2