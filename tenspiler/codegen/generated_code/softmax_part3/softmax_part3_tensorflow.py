####### import statements ########
import tensorflow as tf


def softmax_part3_tf(output, max_pos):
    return tf.reduce_sum(output[:max_pos])


def softmax_part3_tf_glued(output, max_pos):
    output = tf.convert_to_tensor(output, dtype=tf.float32)
    return softmax_part3_tf(output, max_pos)
