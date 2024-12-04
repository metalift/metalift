####### import statements ########
import tensorflow as tf


def transformer_part1_tf(token_position, head1, head_size, key_cache_layer, q):
    return (
        tf.linalg.matvec(
            key_cache_layer[0:token_position][
                :, (head1) * (head_size) : ((head1) * (head_size)) + (head_size)
            ],
            q[(head1) * (head_size) : ((head1) * (head_size)) + (head_size)],
        )
    ) // (tf.sqrt(tf.cast((1) * (head_size), tf.float32)))


def transformer_part1_tf_glued(token_position, head1, head_size, key_cache_layer, q):
    key_cache_layer = tf.convert_to_tensor(key_cache_layer, dtype=tf.int32)
    q = tf.convert_to_tensor(q, dtype=tf.int32)
    return transformer_part1_tf(token_position, head1, head_size, key_cache_layer, q)
