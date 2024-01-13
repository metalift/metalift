from numba import njit


@njit
def multiply_blend_8(base, active):
    output = []
    m = len(base)
    n = len(base[0])
    for i in range(m):
        curr_row = []
        for j in range(n):
            curr_row.append(base[i][j] * active[i][j] / 255)
        output.append(curr_row)
    return output
