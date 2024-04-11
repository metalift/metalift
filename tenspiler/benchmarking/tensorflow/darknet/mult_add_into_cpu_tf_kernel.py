
####### import statements ########
import tensorflow as tf

def mult_add_into_cpu_tf(N, X, Y, Z):
    return (Z[:N]) + ((X[:N]) * (Y[:N]))

def mult_add_into_cpu_tf_glued(N, X, Y, Z):
    X = tf.convert_to_tensor(X, dtype=tf.int32)
    Y = tf.convert_to_tensor(Y, dtype=tf.int32)
    Z = tf.convert_to_tensor(Z, dtype=tf.int32)
    return mult_add_into_cpu_tf(N, X, Y, Z)

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

print("mult_add_into_cpu_tf_kernel")
print(f"{np.average(times)} {np.std(times)}") 
