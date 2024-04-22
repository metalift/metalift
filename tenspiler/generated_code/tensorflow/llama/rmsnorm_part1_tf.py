
####### import statements ########
import tensorflow as tf

def rmsnorm_part1_tf(input, weight):
    return tf.reduce_sum((input) * (input))

def rmsnorm_part1_tf_glued(input, weight):
    input = tf.convert_to_tensor(input, dtype=tf.float32)
    weight = tf.convert_to_tensor(weight, dtype=tf.float32)
    return rmsnorm_part1_tf(input, weight)
