####### import statements ########
import torch


def softmax_part2_torch(input, max_pos, max_val):
    return torch.exp(torch.as_tensor((input[:max_pos]) - (max_val)))


def softmax_part2_torch_glued(input, max_pos, max_val):
    input = torch.tensor(input, dtype=torch.float32)
    return softmax_part2_torch(input, max_pos, max_val)
