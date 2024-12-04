####### import statements ########
import tensorflow as tf


def scale_matrix_tf(m, scale):
    return (scale) * (m)


def scale_matrix_tf_glued(m, scale):
    m = tf.convert_to_tensor(m, dtype=tf.int32)
    return scale_matrix_tf(m, scale)
