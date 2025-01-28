####### import statements ########
import tensorflow as tf


def len_tf(arr, n):
    return tf.reduce_sum((arr[:n]) * (arr[:n]))


def len_tf_glued(arr, n):
    arr = tf.convert_to_tensor(arr, dtype=tf.int32)
    return len_tf(arr, n)
