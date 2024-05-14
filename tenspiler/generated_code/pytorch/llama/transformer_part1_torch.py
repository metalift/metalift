
####### import statements ########
import torch

def transformer_part1_torch (token_position, head1, head_size, key_cache_layer, q):
    return (torch.matmul(torch.transpose(key_cache_layer[0:token_position][:, (head) * (token_position):((head) * (token_position)) + (head_size)], 0, 1), q[(head) * (token_position):((head) * (token_position)) + (head_size)])) / ((0) * (head_size))

def transformer_part1_torch_glued (token_position, head1, head_size, key_cache_layer, q):
    key_cache_layer = torch.tensor(key_cache_layer, dtype=torch.float32)
    q = torch.tensor(q, dtype=torch.float32)
    return transformer_part1_torch(token_position, head1, head_size, key_cache_layer, q)
