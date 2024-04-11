
####### import statements ########
import tensorflow as tf

def vcopy_tf(a, n):
    return a[:n]

def vcopy_tf_glued(a, n):
    a = tf.convert_to_tensor(a, dtype=tf.int32)
    return vcopy_tf(a, n)

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

print("vcopy_tf_kernel")
print(f"{np.average(times)} {np.std(times)}") 
