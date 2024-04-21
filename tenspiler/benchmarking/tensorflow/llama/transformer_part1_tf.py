
####### import statements ########
import tensorflow as tf

def transformer_part1_tf(token_position, head, head_size, key_cache_layer, q):
    return (tf.linalg.matvec(key_cache_layer[:token_position][:, (head) * (head_size):(head) * (head_size) + head_size], q[(head) * (head_size):(head) * (head_size) + head_size])) / (tf.sqrt(tf.cast((head_size) * (1), tf.float32)))

def transformer_part1_tf_glued(token_position, head, head_size, key_cache_layer, q):
    key_cache_layer = tf.convert_to_tensor(key_cache_layer, dtype=tf.float32)
    q = tf.convert_to_tensor(q, dtype=tf.float32)
    return transformer_part1_tf(token_position, head, head_size, key_cache_layer, q)
