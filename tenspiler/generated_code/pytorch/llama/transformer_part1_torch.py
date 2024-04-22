
####### import statements ########
import torch

def transformer_part1_torch (token_position, head, head_size, key_cache_layer, q):
    return (torch.matmul(key_cache_layer[:token_position][:, (head) * (head_size):(head) * (head_size) + head_size], q[(head) * (head_size):(head) * (head_size) + head_size])) / (torch.sqrt(torch.as_tensor((head_size) * (1))))

def transformer_part1_torch_glued (token_position, head, head_size, key_cache_layer, q):
    key_cache_layer = torch.tensor(key_cache_layer, dtype=torch.float32)
    q = torch.tensor(q, dtype=torch.float32)
    return transformer_part1_torch(token_position, head, head_size, key_cache_layer, q)
