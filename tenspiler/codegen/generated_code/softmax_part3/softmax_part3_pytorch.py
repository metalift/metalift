
####### import statements ########
import torch

def softmax_part3_torch (output, max_pos):
    return torch.sum(output[:max_pos])

def softmax_part3_torch_glued (output, max_pos):
    output = torch.tensor(output, dtype=torch.float32)
    return softmax_part3_torch(output, max_pos)
