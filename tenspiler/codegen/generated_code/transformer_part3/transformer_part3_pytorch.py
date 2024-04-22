####### import statements ########
import torch


def transformer_part3_torch(input, hidden_dim):
    return (input[:hidden_dim]) * (
        (1) / ((1) + (torch.exp(torch.as_tensor((0) - (input[:hidden_dim])))))
    )


def transformer_part3_torch_glued(input, hidden_dim):
    input = torch.tensor(input, dtype=torch.float32)
    return transformer_part3_torch(input, hidden_dim)
