import ast
from inspect import signature

from tenspiler.llm.parser import check_func, remove_comments


def fma(x, y, z):
    return x * y + z


def add(x, y):
    return x + y


fma_sign = signature(fma)
add_sign = signature(add)
# get number of arguments of functions
func_sign = {"fma": len(fma_sign.parameters), "add": len(add_sign.parameters)}

# test1 incorrect number of arguments
python_program = """
def test(x,y,z):
    return add(fma(x,y), fma(x,y,z))
"""
# test2 undefined function
python_program2 = """
def test(x,y,z):
    return add(sub(x,y,z), fma(x,y,z))
"""

# test3 correct
python_program3 = """
def test(x,y,z):
    out = add(fma(x,y,z), fma(x,y,z))
    return out
"""

# test4 intermediate results
python_program4 = """
def test(x,y,z):
    a = fma(x,y,z)
    b = fma(x,y,z)
    return add(a, b)
"""

# test5 for loops
python_program5 = """
def test(x,y,z):
    a = fma(x,y,z)
    b = fma(x,y,z)
    for i in range(10):
        a = fma(a,b,a)
    return add(a, b)
"""

# test6 if else
python_program6 = """
def test(x,y,z):
    a = fma(x,y,z)
    b = fma(x,y,z)
    if a > b:
        a = fma(a,b,a)
    else:
        b = fma(a,b,a)
    return add(a, b)
"""

# test7 external libraries
python_program7 = """
def test(x,y,z):
    a = fma(x,y,z)
    b = np.add(a, fma(x,y,z))
    return add(a, b)
"""

# test8 comment
python_program8 = """
def test(x,y,z):
    a = fma(x,y,z)
    b = fma(x,y,z)
    #comment
    return add(a, b)
"""

# test9 multi-line comment
python_program9 = """
def test(x,y,z):
    a = fma(x,y,z)
    b = fma(x,y,z)
    '''comment'''
    return add(a, b)
"""

tests = [
    python_program,
    python_program2,
    python_program3,
    python_program4,
    python_program5,
    python_program6,
    python_program7,
    python_program8,
    python_program9,
]

for test in tests:
    test = remove_comments(test)
    print(f"Testing {test}")
    try:
        tree = ast.parse(test)
        out = check_func(tree, func_sign)
        if out:
            print("Correct")
        else:
            print("Incorrect")
    except Exception as err:
        print(f"Unexpected {err=}, {type(err)=}")
        raise
    print("=" * 100)
