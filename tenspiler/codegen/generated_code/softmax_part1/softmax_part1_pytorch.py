####### import statements ########
import torch


def softmax_part1_torch(input, max_pos):
    return torch.max(input[0:max_pos])


def softmax_part1_torch_glued(input, max_pos):
    input = torch.tensor(input, dtype=torch.float32)
    return softmax_part1_torch(input, max_pos)
