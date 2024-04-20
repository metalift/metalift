
####### import statements ########
import numpy as np

def transformer_part1_np (token_position, head, head_size, key_cache_layer, q):
    return (np.matmul(key_cache_layer[:token_position][:, (head) * (head_size):(head) * (head_size) + head_size], q[(head) * (head_size):(head) * (head_size) + head_size])) / (np.sqrt((head_size) * (1)))

def transformer_part1_np_glued (token_position, head, head_size, key_cache_layer, q):
    key_cache_layer = np.array(key_cache_layer).astype(np.float32)
    q = np.array(q).astype(np.float32)
    return transformer_part1_np(token_position, head, head_size, key_cache_layer, q)
