
####### import statements ########
import tensorflow as tf

def rmsnorm_part2_tf(input, weight, ss):
    return ((1) / (tf.sqrt(tf.cast(((ss) / (tf.size(input, tf.float32))) + (1), tf.float32)))) * ((input) * (weight))

def rmsnorm_part2_tf_glued(input, weight, ss):
    input = tf.convert_to_tensor(input, dtype=tf.float32)
    weight = tf.convert_to_tensor(weight, dtype=tf.float32)
    return rmsnorm_part2_tf(input, weight, ss)
