####### import statements ########
import tensorflow as tf


def matrix_add_matrix_tf(from_matrix, to_matrix):
    return (from_matrix) + (to_matrix)


def matrix_add_matrix_tf_glued(from_matrix, to_matrix):
    from_matrix = tf.convert_to_tensor(from_matrix, dtype=tf.int32)
    to_matrix = tf.convert_to_tensor(to_matrix, dtype=tf.int32)
    return matrix_add_matrix_tf(from_matrix, to_matrix)
