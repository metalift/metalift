####### import statements ########
import tensorflow as tf


def mult_add_into_cpu_tf(N, X, Y, Z):
    return (Z[:N]) + ((X[:N]) * (Y[:N]))


def mult_add_into_cpu_tf_glued(N, X, Y, Z):
    X = tf.convert_to_tensor(X, dtype=tf.int32)
    Y = tf.convert_to_tensor(Y, dtype=tf.int32)
    Z = tf.convert_to_tensor(Z, dtype=tf.int32)
    return mult_add_into_cpu_tf(N, X, Y, Z)
