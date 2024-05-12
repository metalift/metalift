
####### import statements ########
import tensorflow as tf

def matmul_tf(weight, input):
    return tf.linalg.matvec(weight, input)

def matmul_tf_glued(weight, input):
    weight = tf.convert_to_tensor(weight, dtype=tf.float32)
    input = tf.convert_to_tensor(input, dtype=tf.float32)
    return matmul_tf(weight, input)
