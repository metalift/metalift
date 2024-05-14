
####### import statements ########
import torch

def softmax_part4_torch (unnormalized_output, max_pos, sum):
    return (unnormalized_output[:max_pos]) / (sum)

def softmax_part4_torch_glued (unnormalized_output, max_pos, sum):
    unnormalized_output = torch.tensor(unnormalized_output, dtype=torch.float32)
    return softmax_part4_torch(unnormalized_output, max_pos, sum)
