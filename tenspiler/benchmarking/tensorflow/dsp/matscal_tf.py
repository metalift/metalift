
####### import statements ########
import tensorflow as tf

def matscal_tf(mat, val, m, n):
    return (val) * (mat[:m][:, 0:n])

def matscal_tf_glued(mat, val, m, n):
    mat = tf.convert_to_tensor(mat, dtype=tf.int32)
    return matscal_tf(mat, val, m, n)
