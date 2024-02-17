from typing import List


def normal_blend_8(base: List[int], active: List[int], opacity: int) -> List[int]:
    output: List[int] = []
    for i in range(len(base)):
        output.append(opacity * active[i] + (255 - opacity) * base[i])
    return output
