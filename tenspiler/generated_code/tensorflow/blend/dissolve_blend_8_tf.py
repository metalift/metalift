
####### import statements ########
import tensorflow as tf

def dissolve_blend_8_tf(base, active, opacity, rand_cons):
    return tf.where((opacity) - ((((rand_cons) % (100)) + (1)) // (100)) >= 0, active, base)

def dissolve_blend_8_tf_glued(base, active, opacity, rand_cons):
    base = tf.convert_to_tensor(base, dtype=tf.uint8)
    active = tf.convert_to_tensor(active, dtype=tf.uint8)
    return dissolve_blend_8_tf(base, active, opacity, rand_cons)
