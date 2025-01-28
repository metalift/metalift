####### import statements ########
import tensorflow as tf


def matmul_sca_tf(matA, val, m, n):
    return (val) * (matA[:m][:, 0:n])


def matmul_sca_tf_glued(matA, val, m, n):
    matA = tf.convert_to_tensor(matA, dtype=tf.int32)
    return matmul_sca_tf(matA, val, m, n)
