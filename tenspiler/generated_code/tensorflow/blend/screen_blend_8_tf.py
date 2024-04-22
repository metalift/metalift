
####### import statements ########
import tensorflow as tf

def screen_blend_8_tf(base, active):
    return ((base) + (active)) - (((base) * (active)) // (255))

def screen_blend_8_tf_glued(base, active):
    base = tf.convert_to_tensor(base, dtype=tf.uint8)
    active = tf.convert_to_tensor(active, dtype=tf.uint8)
    return screen_blend_8_tf(base, active)
