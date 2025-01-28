from numba import njit


@njit
def darken_blend_8(base, active):
    output = []
    m = len(base)
    n = len(base[0])
    for i in range(m):
        curr_row = []
        for j in range(n):
            if base[i][j] > active[i][j]:
                pixel = active[i][j]
            else:
                pixel = base[i][j]
            curr_row.append(pixel)
        output.append(curr_row)
    return output
