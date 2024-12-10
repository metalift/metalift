# normal_blend_f
normal_blend_f_ps = """
def normal_blend_f(base: List[int], active: List[int], opacity: int) -> List[int]:
    return vec_elemwise_add(vec_scalar_mul(opacity, active), vec_scalar_mul((1 - opacity), base))
"""
normal_blend_f_inv = """
def invariant(base: List[int], active: List[int], i: int, opacity: int, out: List[int]) -> bool:
    return i >= 0 and i <= len(base) and out == vec_elemwise_add(vec_scalar_mul(opacity, active[:i]), vec_scalar_mul(1 - opacity, base[:i]))
"""

# normal_blend_8
normal_blend_8_ps = """
def normal_blend_8(base: List[int], active: List[int], opacity: int) -> List[int]:
    return vec_elemwise_add(vec_scalar_mul(opacity, active), vec_scalar_mul((32 - opacity), base))
"""
normal_blend_8_inv = """
def invariant(base: List[int], active: List[int], i: int, opacity: int, out: List[int]) -> bool:
    return i >= 0 and i <= len(base) and out == vec_elemwise_add(vec_scalar_mul(opacity, active[:i]), vec_scalar_mul(32 - opacity, base[:i]))
"""

# dissolve_blend_8
dissolve_blend_8_ps = """
def dissolve_blend_8(base: List[List[int]], active: List[List[int]], opacity: int, rand_cons: int) -> List[List[int]]:
    return matrix_selection_two_args(base, active, lambda base_pixel, active_pixel: active_pixel if opacity - ((rand_cons % 100) + 1) // 100 >= 0 else base_pixel)
"""
dissolve_blend_8_inv = """
def invariant1(base: List[List[int]], active: List[List[int]], opacity: int, out: List[List[int]], rand_cons: int, row: int) -> bool:
    return row >= 0 and row <= len(base) and out == matrix_selection_two_args( base[:row], active[:row], lambda base_pixel, active_pixel: active_pixel if opacity - ((rand_cons % 100) + 1) // 100 >= 0 else base_pixel)

def invariant2(base: List[List[int]], active: List[List[int]], col: int, opacity: int, out: List[List[int]], rand_cons: int, row: int, row_vec: List[int]) -> bool:
    return row >= 0 and row < len(base) and col >= 0 and col <= len(base[0]) and row_vec == selection_two_args( base[row][:col], active[row][:col], lambda base_pixel, active_pixel: active_pixel if opacity - ((rand_cons % 100) + 1) // 100 >= 0 else base_pixel) and out == matrix_selection_two_args( base[:row], active[:row], lambda base_pixel, active_pixel: active_pixel if opacity - ((rand_cons % 100) + 1) // 100 >= 0 else base_pixel)
"""

# darken_blend_8
darken_blend_8_ps = """
def darken_blend_8(base: List[List[int]], active: List[List[int]]) -> List[List[int]]:
    return matrix_selection_two_args(base, active, lambda x, y: ite_int_int(x > y, y, x))
"""
darken_blend_8_inv = """
def invariant1(row: int, base: List[List[int]], active: List[List[int]], out: List[List[int]]) -> bool:
    return row >= 0 and row <= len(base) and out == matrix_selection_two_args(base[:row], active[:row], lambda x, y: ite_int_int(x > y, y, x))

def invariant2(row: int, col: int, base: List[List[int]], active: List[List[int]], row_vec: List[int], out: List[List[int]]) -> bool:
    return row >= 0 and row < len(base) and col >= 0 and col <= len(base[0]) and \
        row_vec == selection_two_args(base[row][:col], active[row][:col], lambda x, y: ite_int_int(x > y, y, x)) and \
        out == matrix_selection_two_args(base[:row], active[:row], lambda x, y: ite_int_int(x > y, y, x))
"""

# multiply_blend_8
multiply_blend_8_ps = """
def multiply_blend_8(base: List[List[int]], active: List[List[int]]) -> List[List[int]]:
    return matrix_scalar_div(32, matrix_elemwise_mul(base, active))
"""
multiply_blend_8_inv = """
def invariant1(active: List[List[int]], base: List[List[int]], out: List[List[int]], row: int) -> bool:
    return row >= 0 and row <= len(base) and out == matrix_scalar_div(32, matrix_elemwise_mul(matrix_row_slice(base, 0, row), matrix_row_slice(active, 0, row)))

def invariant2(active: List[List[int]], base: List[List[int]], col: int, out: List[List[int]], row: int, row_vec: List[int]) -> bool:
    return col >= 0 and col <= len(base[0]) and row >= 0 and row < len(base) and out == matrix_scalar_div(32, matrix_elemwise_mul(matrix_row_slice(base, 0, row), matrix_row_slice(active, 0, row))) and row_vec == vec_scalar_div(32, vec_elemwise_mul(vec_slice(base[row], 0, col), vec_slice(active[row], 0, col)))
"""

# linear_burn_8
linear_burn_8_ps = """
def linear_burn_8(base: List[List[int]], active: List[List[int]]) -> List[List[int]]:
    return matrix_scalar_sub(32, matrix_elemwise_add(base, active))
"""
linear_burn_8_inv = """
def invariant1(active: List[List[int]], base: List[List[int]], out: List[List[int]], row: int) -> bool:
    return row >= 0 and row <= len(base) and out == matrix_scalar_sub(32, matrix_elemwise_add(matrix_row_slice(base, 0, row), matrix_row_slice(active, 0, row)))

def invariant2(active: List[List[int]], base: List[List[int]], col: int, out: List[List[int]], row: int, row_vec: List[int]) -> bool:
    return col >= 0 and col <= len(base[0]) and row >= 0 and row < len(base) and out == matrix_scalar_sub(32, matrix_elemwise_add(matrix_row_slice(base, 0, row), matrix_row_slice(active, 0, row))) and row_vec == vec_scalar_sub(32, vec_elemwise_add(vec_slice(base[row], 0, col), vec_slice(active[row], 0, col)))
"""

# color_burn_8
color_burn_8_ps = """
def color_burn_8(base: List[List[int]], active: List[List[int]]) -> List[List[int]]:
    return matrix_selection_two_args(base, active, lambda x, y: ite_int_int(y == 0, 32, 32 - (32 - x) // y))
"""
color_burn_8_inv = """
def invariant1(row: int, base: List[List[int]], active: List[List[int]], out: List[List[int]]) -> bool:
    return row >= 0 and row <= len(base) and out == matrix_selection_two_args(base[:row], active[:row], lambda x, y: ite_int_int(y == 0, 32, 32 - (32 - x) // y))

def invariant2(row: int, col: int, base: List[List[int]], active: List[List[int]], row_vec: List[int], out: List[List[int]]) -> bool:
    return row >= 0 and row < len(base) and col >= 0 and col <= len(base[0]) and \
        row_vec == selection_two_args(base[row][:col], active[row][:col], lambda x, y: ite_int_int(y == 0, 32, 32 - (32 - x) // y)) and \
        out == matrix_selection_two_args(base[:row], active[:row], lambda x, y: ite_int_int(y == 0, 32, 32 - (32 - x) // y))
"""

# lighten_blend_8
lighten_blend_8_ps = """
def lighten_blend_8(base: List[List[int]], active: List[List[int]]) -> List[List[int]]:
    return matrix_selection_two_args(base, active, lambda x, y: ite_int_int(x < y, y, x))
"""
lighten_blend_8_inv = """
def invariant1(row: int, base: List[List[int]], active: List[List[int]], out: List[List[int]]) -> bool:
    return row >= 0 and row <= len(base) and out == matrix_selection_two_args(base[:row], active[:row], lambda x, y: ite_int_int(x < y, y, x))

def invariant2(row: int, col: int, base: List[List[int]], active: List[List[int]], row_vec: List[int], out: List[List[int]]) -> bool:
    return row >= 0 and row < len(base) and col >= 0 and col <= len(base[0]) and \
        row_vec == selection_two_args(base[row][:col], active[row][:col], lambda x, y: ite_int_int(x < y, y, x)) and \
        out == matrix_selection_two_args(base[:row], active[:row], lambda x, y: ite_int_int(x < y, y, x))
"""

# screen_blend_8
screen_blend_8_ps = """
def screen_blend_8(base: List[List[int]], active: List[List[int]]) -> List[List[int]]:
    return matrix_elemwise_sub(
        matrix_elemwise_add(base, active),
        matrix_scalar_div(
            32,
            matrix_elemwise_mul(base, active),
        )
    )
"""
screen_blend_8_inv = """
def invariant1(base: List[List[int]], active: List[List[int]], out: List[List[int]], row: int) -> bool:
    return row >= 0 and row <= len(base) and out == matrix_elemwise_sub(matrix_elemwise_add(base, active),matrix_scalar_div(32, matrix_elemwise_mul(base[:row], active[:row])))

def invariant2(base: List[List[int]], active: List[List[int]], col: int, out: List[List[int]], row: int, row_vec: List[int]) -> bool:
    return col >= 0 and col <= len(base[0]) and row >= 0 and row <= len(base) and out == matrix_elemwise_sub(matrix_elemwise_add(base[:row], active[:row]),matrix_scalar_div(32, matrix_elemwise_mul(base[:row], active[:row]))) and row_vec == vec_elemwise_sub(vec_elemwise_add(base[row][:col], active[row][:col]),vec_scalar_div(32, vec_elemwise_mul(base[row][:col], active[row][:col])))
"""

# linear_dodge_8
linear_dodge_8_ps = """
def linear_dodge_8(base: List[List[int]], active: List[List[int]]) -> List[List[int]]:
    return matrix_elemwise_add(base, active)
"""
linear_dodge_8_inv = """
def invariant1(row: int, base: List[List[int]], active: List[List[int]], out: List[List[int]]) -> bool:
    return row >= 0 and row <= len(base) and out == matrix_elemwise_add(base[:row], active[:row])

def invariant2(row: int, col: int, base: List[List[int]], active: List[List[int]], row_vec: List[int], out: List[List[int]]) -> bool:
    return row >= 0 and row < len(base) and col >= 0 and col <= len(base[0]) and \
        row_vec == vec_elemwise_add(base[row][:col], active[row][:col]) and \
        out == matrix_elemwise_add(base[:row], active[:row])
"""

# color_dodge_8
color_dodge_8_ps = """
def color_dodge_8(base: List[List[int]], active: List[List[int]]) -> List[List[int]]:
    return matrix_selection_two_args(
        active,
        matrix_elemwise_div(base, scalar_matrix_sub(32, active)),
        lambda a, b: ite_int(a == 32, 32, b)
    )
"""
color_dodge_8_inv = """
def invariant1(row: int, base: List[List[int]], active: List[List[int]], out: List[List[int]]) -> bool:
    return row >= 0 and row <= len(base) and out == matrix_selection_two_args(active[:row], matrix_elemwise_div(base[:row], scalar_matrix_sub(32, active[:row])), lambda a, b: ite_int(a == 32, 32, b))

def invariant2(row: int, col: int, base: List[List[int]], active: List[List[int]], row_vec: List[int], out: List[List[int]]) -> bool:
    return row >= 0 and row < len(base) and col >= 0 and col <= len(base[0]) and \
        row_vec == selection_two_args(active[row][:col], vec_elemwise_div(base[row][:col], scalar_vec_sub(32, active[row][:col])), lambda a, b: ite_int(a == 32, 32, b)) and \
        out == matrix_selection_two_args(active[:row], matrix_elemwise_div(base[:row], scalar_matrix_sub(32, active[:row])), lambda a, b: ite_int(a == 32, 32, b))
"""

# overlay_blend_8
overlay_blend_8_ps = """
def overlay_blend_8(base: List[List[int]], active: List[List[int]]) -> List[List[int]]:
    return matrix_selection_two_args(
        base,
        active,
        lambda x, y: ite_int(
            x >= 128,
            2 * x + x - 2 * x * x // 32 - 32,
            2 * x * x // 32,
        ),
    )
"""
overlay_blend_8_inv = """
def invariant1(row: int, base: List[List[int]], active: List[List[int]], out: List[List[int]]) -> bool:
    return row >= 0 and row <= len(base) and out == matrix_selection_two_args(base[:row], active[:row], lambda x, y: ite_int(x >= 128, 2 * x + x - 2 * x * x // 32 - 32, 2 * x * x // 32))

def invariant2(row: int, col: int, base: List[List[int]], active: List[List[int]], row_vec: List[int], out: List[List[int]]) -> bool:
    return row >= 0 and row < len(base) and col >= 0 and col <= len(base[0]) and \
        row_vec == selection_two_args(base[row][:col], active[row][:col], lambda x, y: ite_int(x >= 128, 2 * x + x - 2 * x * x // 32 - 32, 2 * x * x // 32)) and \
        out == matrix_selection_two_args(base[:row], active[:row], lambda x, y: ite_int(x >= 128, 2 * x + x - 2 * x * x // 32 - 32, 2 * x * x // 32))
"""

correct_sols = {
    "normal_blend_f": {"ps": normal_blend_f_ps, "inv": normal_blend_f_inv},
    "normal_blend_8": {"ps": normal_blend_8_ps, "inv": normal_blend_8_inv},
    "dissolve_blend_8": {"ps": dissolve_blend_8_ps, "inv": dissolve_blend_8_inv},
    "darken_blend_8": {"ps": darken_blend_8_ps, "inv": darken_blend_8_inv},
    "multiply_blend_8": {"ps": multiply_blend_8_ps, "inv": multiply_blend_8_inv},
    "linear_burn_8": {"ps": linear_burn_8_ps, "inv": linear_burn_8_inv},
    "color_burn_8": {"ps": color_burn_8_ps, "inv": color_burn_8_inv},
    "lighten_blend_8": {"ps": lighten_blend_8_ps, "inv": lighten_blend_8_inv},
    "screen_blend_8": {"ps": screen_blend_8_ps, "inv": screen_blend_8_inv},
    "linear_dodge_8": {"ps": linear_dodge_8_ps, "inv": linear_dodge_8_inv},
    "color_dodge_8": {"ps": color_dodge_8_ps, "inv": color_dodge_8_inv},
    "overlay_blend_8": {"ps": overlay_blend_8_ps, "inv": overlay_blend_8_inv},
}
