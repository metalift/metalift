
####### import statements ########
import mlx.core as mx

def transformer_part2_mx (token_position, head1, head_size, key_cache_layer, attention):
    return mx.matmul(mx.transpose(key_cache_layer[0:(token_position) + (1)][:, (head1) * (head_size):((head1) * (head_size)) + (head_size)]), attention[0:(token_position) + (1)])

def transformer_part2_mx_glued (token_position, head1, head_size, key_cache_layer, attention):
    key_cache_layer = mx.array(key_cache_layer, mx.float32)
    attention = mx.array(attention, mx.float32)
    return transformer_part2_mx(token_position, head1, head_size, key_cache_layer, attention)
