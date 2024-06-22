from typing import List


def elemwise_add(
    tensor_a: List[List[List[int]]], tensor_b: List[List[List[int]]]
) -> List[List[List[int]]]:
    result: List[List[List[int]]] = []

    # Each element of tensor_a is a matrix
    for i in range(len(tensor_a)):
        curr_matrix: List[List[int]] = []
        # Each element of tensor_a[0] is a list
        for j in range(len(tensor_a[0])):
            curr_lst: List[int] = []
            for k in range(len(tensor_a[0][0])):
                curr_lst.append(tensor_a[i][j][k] + tensor_b[i][j][k])
            curr_matrix.append(curr_lst)
        result.append(curr_matrix)

    return result
