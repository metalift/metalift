from typing import List


def dot_1d(input: List[int], kernel: List[int]) -> int:
    if not kernel:
        return 0

    return input[0] * kernel[0] + dot_1d(input[1:], kernel[1:])


def dot_2d(input: List[List[int]], kernel: List[List[int]]) -> int:
    if not kernel:
        return 0

    return dot_1d(input[0], kernel[0]) + dot_2d(input[1:], kernel[1:])


def conv_inner(
    inp: List[List[int]], kernel: List[List[int]], i: int, j: int
) -> List[int]:
    if j >= len(inp[i]):
        return []

    return [dot_2d(inp[i:], kernel)] + conv_inner(inp, kernel, i, j + 1)


def conv2d(inp: List[List[int]], kernel: List[List[int]]) -> List[List[int]]:
    def conv2d_helper(inp, kernel, i, j):
        if i >= len(inp):
            return []

        return [conv_inner(inp, kernel, i, j)] + conv2d_helper(inp, kernel, i + 1, j)

    return conv2d_helper(inp, kernel, 0, 0)


constants = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]
