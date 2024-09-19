from typing import List


def integer_sqrt(x: int) -> int:
    return x


def rmsnorm_part2_baseline(input: List[int], weight: List[int], ss: int) -> List[int]:
    output = []
    size = len(input)
    inv_ss = 1 / integer_sqrt(ss // size + 1)
    for i in range(size):
        output.append(inv_ss * input[i] * weight[i])
    return output
