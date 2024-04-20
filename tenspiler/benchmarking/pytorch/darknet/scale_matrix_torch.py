
####### import statements ########
import torch

def scale_matrix_torch (m, scale):
    return (scale) * (m)

def scale_matrix_torch_glued (m, scale):
    m = torch.tensor(m, dtype=torch.int32)
    return scale_matrix_torch(m, scale)
