
####### import statements ########
import numpy as np

def transformer_part1_np (token_position, head1, head_size, key_cache_layer, q):
    return (np.matmul(np.transpose(key_cache_layer[0:token_position][:, (head) * (token_position):((head) * (token_position)) + (head_size)]), q[(head) * (token_position):((head) * (token_position)) + (head_size)])) / ((0) * (head_size))

def transformer_part1_np_glued (token_position, head1, head_size, key_cache_layer, q):
    key_cache_layer = np.array(key_cache_layer).astype(np.float32)
    q = np.array(q).astype(np.float32)
    return transformer_part1_np(token_position, head1, head_size, key_cache_layer, q)
