
####### import statements ########
import torch

def matrix_add_matrix_torch (from_matrix, to_matrix):
    return (to_matrix) + (from_matrix)

def matrix_add_matrix_torch_glued (from_matrix, to_matrix):
    from_matrix = torch.tensor(from_matrix, dtype=torch.int32)
    to_matrix = torch.tensor(to_matrix, dtype=torch.int32)
    return matrix_add_matrix_torch(from_matrix, to_matrix)
