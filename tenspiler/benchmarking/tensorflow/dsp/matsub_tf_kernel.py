
####### import statements ########
import tensorflow as tf

def matsub_tf(matA, matB, m, n):
    return (matA[:m][:, 0:n]) - (matB[:m][:, 0:n])

def matsub_tf_glued(matA, matB, m, n):
    matA = tf.convert_to_tensor(matA, dtype=tf.int32)
    matB = tf.convert_to_tensor(matB, dtype=tf.int32)
    return matsub_tf(matA, matB, m, n)

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

print("matsub_tf_kernel")
print(f"{np.average(times)} {np.std(times)}") 
