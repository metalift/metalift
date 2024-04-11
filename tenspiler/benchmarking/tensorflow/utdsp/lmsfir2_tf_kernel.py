
####### import statements ########
import tensorflow as tf

def lmsfir2_tf(NTAPS, input, coefficient, error):
    return (coefficient[:(NTAPS) - (1)]) + ((error) * (input[:(NTAPS) - (1)]))

def lmsfir2_tf_glued(NTAPS, input, coefficient, error):
    input = tf.convert_to_tensor(input, dtype=tf.int32)
    coefficient = tf.convert_to_tensor(coefficient, dtype=tf.int32)
    return lmsfir2_tf(NTAPS, input, coefficient, error)

####### more import statements for benchmarking ########
import time
import cv2
import os
import numpy as np

####### setup for benchmarking ########
rng = np.random.default_rng(1)

folder = "./data/"

img_files = [os.path.join(folder, f) for f in os.listdir(folder) if os.path.isfile(os.path.join(folder, f))]

bases = []
actives = []

for _file in img_files:
    img = cv2.imread(_file, cv2.IMREAD_GRAYSCALE).astype(np.uint8)
    rnd = (rng.random(img.shape, dtype = np.float32) * 255).astype(np.uint8)
    bases.append(img)
    actives.append(rnd)

print("lmsfir2_tf_kernel")
print(f"{np.average(times)} {np.std(times)}") 
