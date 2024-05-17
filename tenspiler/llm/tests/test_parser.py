# import pytest

from metalift.frontend.llvm import Driver
from metalift.ir import Int, List, call, fn_decl_recursive
from metalift.vc_util import and_objects
from tenspiler.llm.parser import check_solution

check_solution(None, 1)
exit(0)
# def fma(x, y, z):
#     return x * y + z


# def add(x, y):
#     return x + y


# fma_sign = signature(fma)
# add_sign = signature(add)
# # get number of arguments of functions
# func_sign = {"fma": len(fma_sign.parameters), "add": len(add_sign.parameters)}

# # test1 incorrect number of arguments
# python_program = """
# def test(x,y,z):
#     return add(fma(x,y), fma(x,y,z))
# """
# # test2 undefined function
# python_program2 = """
# def test(x,y,z):
#     return add(sub(x,y,z), fma(x,y,z))
# """

# # test3 correct
# python_program3 = """
# def test(x,y,z):
#     out = add(fma(x,y,z), fma(x,y,z))
#     return out
# """

# # test4 intermediate results
# python_program4 = """
# def test(x,y,z):
#     a = fma(x,y,z)
#     b = fma(x,y,z)
#     return add(a, b)
# """

# # test5 for loops
# python_program5 = """
# def test(x,y,z):
#     a = fma(x,y,z)
#     b = fma(x,y,z)
#     for i in range(10):
#         a = fma(a,b,a)
#     return add(a, b)
# """

# # test6 if else
# python_program6 = """
# def test(x,y,z):
#     a = fma(x,y,z)
#     b = fma(x,y,z)
#     if a > b:
#         a = fma(a,b,a)
#     else:
#         b = fma(a,b,a)
#     return add(a, b)
# """

# # test7 external libraries
# python_program7 = """
# def test(x,y,z):
#     a = fma(x,y,z)
#     b = np.add(a, fma(x,y,z))
#     return add(a, b)
# """

# # test8 comment
# python_program8 = """
# def test(x,y,z):
#     a = fma(x,y,z)
#     b = fma(x,y,z)
#     #comment
#     return add(a, b)
# """

# # test9 multi-line comment
# python_program9 = """
# def test(x,y,z):
#     a = fma(x,y,z)
#     b = fma(x,y,z)
#     '''comment'''
#     return add(a, b)
# """

# tests = [
#     python_program,
#     python_program2,
#     python_program3,
#     python_program4,
#     python_program5,
#     python_program6,
#     python_program7,
#     python_program8,
#     python_program9,
# ]


def test_correct_normal_blend_f():
    prog = """
    def normal_blend_8(base: List[int], active: List[int], opacity: int) -> List[int]:
        return vec_elemwise_add(vec_scalar_mul(opacity, active), vec_scalar_mul(255 - opacity, base))
    """
    base = List(Int, "base")
    active = List(Int, "active")
    opacity = Int("opacity")

    expected_ir = fn_decl_recursive(
        "normal_blend_8",
        List[Int],
        call(
            "vec_elemwise_add",
            List[Int],
            call("vec_scalar_mul", List[Int], opacity, active),
            call("vec_scalar_mul", List[Int], 255 - opacity, base),
        ),
        base,
        active,
        opacity,
    )
    actual_ir = _test_prog(prog)
    assert actual_ir == expected_ir


def test_incorrect_darken_blend_8_with_min():
    prog = """
    def darken_blend_8(base: List[List[int]], active: List[List[int]]) -> List[List[int]]:
        return matrix_selection_two_args(base, active, min)
    """
    with pytest.raises(Exception):
        _test_prog(prog)


def test_correct_multiply_blend_8():
    prog = """
    def multiply_blend_8(base: List[List[int]], active: List[List[int]]) -> List[List[int]]:
        return matrix_scalar_div(255, matrix_elemwise_mul(base, active))
    """
    base, active = List(List[Int], "base"), List(List[Int], "active")
    expected_ir = fn_decl_recursive(
        "multiply_blend_8",
        List[List[Int]],
        call(
            "matrix_scalar_div",
            List[List[Int]],
            Int(255),
            call("matrix_elemwise_mul", List[List[Int]], base, active),
        ),
        base,
        active,
    )
    actual_ir = _test_prog(prog)
    assert actual_ir == expected_ir


def test_incorrect_multiply_blend_8_with_unknown_func_call():
    prog = """
    def multiply_blend_8(base: List[List[int]], active: List[List[int]]) -> List[List[int]]:
        return matrix_map(matrix_scalar_div(255, matrix_elemwise_mul(base, active)), lambda x: int(x))
    """
    with pytest.raises(Exception):
        _test_prog(prog)


def test_incorrect_multiply_blend_8_with_wrong_type():
    prog = """
    def multiply_blend_8(base: List[List[int]], active: List[List[int]]) -> List[List[int]]:
        return matrix_scalar_div(255, vec_map(
            matrix_elemwise_mul(base, active),
            lambda x: x // 255
        ))
    """
    with pytest.raises(Exception):
        _test_prog(prog)


def test_correct_syntax_linear_burn_8():
    prog = """
    def linear_burn_8(base: List[List[int]], active: List[List[int]]) -> List[List[int]]:
        return matrix_elemwise_sub(matrix_elemwise_add(base, active), matrix_scalar_add(255, []))
    """
    _test_prog(prog)


def test_incorrect_linear_burn_8_with_invalid_list_constr():
    prog = """
    def linear_burn_8(base: List[List[int]], active: List[List[int]]) -> List[List[int]]:
        return matrix_elemwise_sub(matrix_elemwise_add(base, active), matrix_scalar_mul(255, [[1]*len(base[0])]*len(base)))
    """
    with pytest.raises(Exception):
        _test_prog(prog)


def test_correct_color_burn_8():
    prog = """
    def color_burn_8(base: List[List[int]], active: List[List[int]]) -> List[List[int]]:
        return matrix_selection_two_args(
            base,
            active,
            lambda b, a: 255 if a == 0 else 255 - (255 - b) // a
        )
    """
    fn_decls, in_calls = _test_prog(prog)
    # import pdb; pdb.set_trace()


# tests = [correct_normal_blend_f_prog]
# target_func_def, func_sigs, types = mypy_parse(correct_normal_blend_f_prog)
# fn_decl_ir = mypy_node_to_ir(target_func_def, func_sigs, types)

# print(fn_decl_ir)
# exit(0)

# for test in tests:
#     test = remove_comments(test)
#     print(f"Testing {test}")
#     try:
#         tree = ast.parse(test)
#         out = check_func(tree, func_sigs)
#         if out:
#             print("Correct")
#         else:
#             print("Incorrect")
#     except Exception as err:
#         print(f"Unexpected {err=}, {type(err)=}")
#         raise
#     print("=" * 100)
