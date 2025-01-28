####### import statements ########
import tensorflow as tf


def matadd_tf(matA, matB, m, n):
    return (matA[:m][:, 0:n]) + (matB[:m][:, 0:n])


def matadd_tf_glued(matA, matB, m, n):
    matA = tf.convert_to_tensor(matA, dtype=tf.int32)
    matB = tf.convert_to_tensor(matB, dtype=tf.int32)
    return matadd_tf(matA, matB, m, n)
