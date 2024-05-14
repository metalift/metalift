
####### import statements ########
import torch

def transformer_part1_torch (token_position, head1, head_size, key_cache_layer, q):
    return (torch.matmul(key_cache_layer[0:token_position][:, (head1) * (head_size):((head1) * (head_size)) + (head_size)], q[(head1) * (head_size):((head1) * (head_size)) + (head_size)])) / (torch.sqrt(torch.as_tensor((1) * (head_size))))

def transformer_part1_torch_glued (token_position, head1, head_size, key_cache_layer, q):
    key_cache_layer = torch.tensor(key_cache_layer, dtype=torch.float32)
    q = torch.tensor(q, dtype=torch.float32)
    return transformer_part1_torch(token_position, head1, head_size, key_cache_layer, q)
