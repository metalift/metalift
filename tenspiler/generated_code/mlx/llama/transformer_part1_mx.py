
####### import statements ########
import mlx.core as mx

def transformer_part1_mx (token_position, head1, head_size, key_cache_layer, q):
    return (mx.matmul(key_cache_layer[0:token_position][:, (head1) * (head_size):((head1) * (head_size)) + (head_size)], q[(head1) * (head_size):((head1) * (head_size)) + (head_size)])) / (mx.sqrt(mx.array((1) * (head_size))))

def transformer_part1_mx_glued (token_position, head1, head_size, key_cache_layer, q):
    key_cache_layer = mx.array(key_cache_layer, mx.float32)
    q = mx.array(q, mx.float32)
    return transformer_part1_mx(token_position, head1, head_size, key_cache_layer, q)
