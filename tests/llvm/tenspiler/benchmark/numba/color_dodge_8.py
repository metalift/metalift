from numba import njit


@njit
def color_dodge_8(base, active):
    output = []
    m = len(base)
    n = len(base[0])
    for i in range(m):
        curr_row = []
        for j in range(n):
            if active[i][j] == 255:
                pixel = 255
            else:
                pixel = base[i][j] / (255 - active[i][j])
            curr_row.append(pixel)
        output.append(curr_row)
    return output
