
####### import statements ########
import tensorflow as tf

def softmax_part2_tf(input, max_pos, max_val):
    return tf.exp((input[:max_pos]) - (max_val))

def softmax_part2_tf_glued(input, max_pos, max_val):
    input = tf.convert_to_tensor(input, dtype=tf.float32)
    return softmax_part2_tf(input, max_pos, max_val)
