####### import statements ########
import tensorflow as tf


def sum_of_squares_tf(arr, n):
    return tf.reduce_sum((arr[:n]) * (arr[:n]))


def sum_of_squares_tf_glued(arr, n):
    arr = tf.convert_to_tensor(arr, dtype=tf.int32)
    return sum_of_squares_tf(arr, n)
