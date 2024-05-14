
####### import statements ########
import tensorflow as tf

def transformer_part1_tf(token_position, head1, head_size, key_cache_layer, q):
    return (tf.linalg.matvec(tf.transpose(key_cache_layer[0:token_position][:, (head) * (token_position):((head) * (token_position)) + (head_size)]), q[(head) * (token_position):((head) * (token_position)) + (head_size)])) / ((0) * (head_size))

def transformer_part1_tf_glued(token_position, head1, head_size, key_cache_layer, q):
    key_cache_layer = tf.convert_to_tensor(key_cache_layer, dtype=tf.float32)
    q = tf.convert_to_tensor(q, dtype=tf.float32)
    return transformer_part1_tf(token_position, head1, head_size, key_cache_layer, q)
