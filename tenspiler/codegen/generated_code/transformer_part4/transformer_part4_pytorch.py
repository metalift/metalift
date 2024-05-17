
####### import statements ########
import torch

def transformer_part4_torch (input1, input2, hidden_dim):
    return (input1[:hidden_dim]) * (input2[:hidden_dim])

def transformer_part4_torch_glued (input1, input2, hidden_dim):
    input1 = torch.tensor(input1, dtype=torch.float32)
    input2 = torch.tensor(input2, dtype=torch.float32)
    return transformer_part4_torch(input1, input2, hidden_dim)
