
####### import statements ########
import tensorflow as tf

def gemv_tf(M, N, A, x):
    return tf.linalg.matvec(A[:M][:, 0:N], x[:N])

def gemv_tf_glued(M, N, A, x):
    A = tf.convert_to_tensor(A, dtype=tf.int32)
    x = tf.convert_to_tensor(x, dtype=tf.int32)
    return gemv_tf(M, N, A, x)
