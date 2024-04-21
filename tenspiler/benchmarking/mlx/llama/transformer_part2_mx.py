
####### import statements ########
import mlx.core as mx

def transformer_part2_mx (token_position, head, head_size, key_cache_layer, attention):
    return mx.matmul(mx.transpose(key_cache_layer[:(token_position) + (1)][:, (head) * (head_size):(head) * (head_size) + head_size]), attention[:(token_position) + (1)])

def transformer_part2_mx_glued (token_position, head, head_size, key_cache_layer, attention):
    key_cache_layer = mx.array(key_cache_layer, mx.float32)
    attention = mx.array(attention, mx.float32)
    return transformer_part2_mx(token_position, head, head_size, key_cache_layer, attention)
