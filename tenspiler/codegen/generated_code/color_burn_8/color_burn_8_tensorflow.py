
####### import statements ########
import tensorflow as tf

def color_burn_8_tf(base, active):
    return tf.where(tf.equal(active, 0), 32, (32) - (((32) - (base)) // (active)))

def color_burn_8_tf_glued(base, active):
    base = tf.convert_to_tensor(base, dtype=tf.uint8)
    active = tf.convert_to_tensor(active, dtype=tf.uint8)
    return color_burn_8_tf(base, active)
