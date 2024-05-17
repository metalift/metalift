
####### import statements ########
import torch

def transformer_part2_torch (token_position, head1, head_size, key_cache_layer, attention):
    return torch.matmul(torch.transpose(key_cache_layer[0:(token_position) + (1)][:, (head1) * (head_size):((head1) * (head_size)) + (head_size)], 0, 1), attention[0:(token_position) + (1)])

def transformer_part2_torch_glued (token_position, head1, head_size, key_cache_layer, attention):
    key_cache_layer = torch.tensor(key_cache_layer, dtype=torch.float32)
    attention = torch.tensor(attention, dtype=torch.float32)
    return transformer_part2_torch(token_position, head1, head_size, key_cache_layer, attention)
