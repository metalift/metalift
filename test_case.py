# normal_blend_f
normal_blend_f_ps = """
def normal_blend_f(base: List[int], active: List[int], opacity: int) -> List[int]:
    return vec_elemwise_add(vec_scalar_mul(opacity, active), vec_scalar_mul((1 - opacity), base))
"""
normal_blend_f_inv = """
"""
# darken_blend_8
darken_blend_ps = """
def darken_blend_8(base: List[List[int]], active: List[List[int]]) -> List[List[int]]:
    return matrix_selection_two_args(base, active, lambda x, y: ite_int(x > y, y, x))
"""
darken_blend_inv = """
def invariant1(row: int, base: List[List[int]], active: List[List[int]], out: List[List[int]]) -> bool:
    return row >= 0 and row <= len(base) and out == matrix_selection_two_args(base[:row], active[:row], lambda x, y: ite_int(x > y, y, x))

def invariant2(row: int, col: int, base: List[List[int]], active: List[List[int]], row_vec: List[int], out: List[List[int]]) -> bool:
    return row >= 0 and row < len(base) and col >= 0 and col <= len(base[0]) and \
        row_vec == selection_two_args(base[row][:col], active[row][:col], lambda x, y: ite_int(x > y, y, x)) and \
        out == matrix_selection_two_args(base[:row], active[:row], lambda x, y: ite_int(x > y, y, x))
"""

# linear_dodge_8
linear_dodge_ps = """
def linear_dodge_8(base: List[List[int]], active: List[List[int]]) -> List[List[int]]:
    return matrix_elemwise_add(base, active)
"""
linear_dodge_inv = """
def invariant1(row: int, base: List[List[int]], active: List[List[int]], out: List[List[int]]) -> bool:
    return row >= 0 and row <= len(base) and out == matrix_elemwise_add(base[:row], active[:row])

def invariant2(row: int, col: int, base: List[List[int]], active: List[List[int]], row_vec: List[int], out: List[List[int]]) -> bool:
    return row >= 0 and row < len(base) and col >= 0 and col <= len(base[0]) and \
        row_vec == vec_elemwise_add(base[row][:col], active[row][:col]) and \
        out == matrix_elemwise_add(base[:row], active[:row])
"""

correct_sols = {
    "darken_blend_8": {"ps": darken_blend_ps, "inv": darken_blend_inv},
    "linear_dodge_8": {"ps": linear_dodge_ps, "inv": linear_dodge_inv},
}
