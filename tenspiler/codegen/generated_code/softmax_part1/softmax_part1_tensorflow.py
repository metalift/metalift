
####### import statements ########
import tensorflow as tf

def softmax_part1_tf(input, max_pos):
    return tf.reduce_max(input[0:max_pos])

def softmax_part1_tf_glued(input, max_pos):
    input = tf.convert_to_tensor(input, dtype=tf.float32)
    return softmax_part1_tf(input, max_pos)
