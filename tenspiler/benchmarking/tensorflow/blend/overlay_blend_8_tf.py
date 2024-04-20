
####### import statements ########
import tensorflow as tf

def overlay_blend_8_tf(base, active):
    return tf.where(tf.greater_equal(base, 128), ((((2) * (base)) + (base)) - ((((2) * (base)) * (base)) // (255))) - (255), (((2) * (base)) * (base)) // (255))

def overlay_blend_8_tf_glued(base, active):
    base = tf.convert_to_tensor(base, dtype=tf.uint8)
    active = tf.convert_to_tensor(active, dtype=tf.uint8)
    return overlay_blend_8_tf(base, active)
