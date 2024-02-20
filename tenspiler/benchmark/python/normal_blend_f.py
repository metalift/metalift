from typing import List


def normal_blend_f(base: List[int], active: List[int], opacity: int) -> List[int]:
    output: List[int] = []
    for i in range(len(base)):
        output.append(opacity * active[i] + (1 - opacity) * base[i])
    return output
