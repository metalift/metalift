####### import statements ########
import tensorflow as tf


def mat1x3_tf(N, h, x):
    return tf.linalg.matvec(h[:N][:, 0:N], x[:N])


def mat1x3_tf_glued(N, h, x):
    h = tf.convert_to_tensor(h, dtype=tf.int32)
    x = tf.convert_to_tensor(x, dtype=tf.int32)
    return mat1x3_tf(N, h, x)
