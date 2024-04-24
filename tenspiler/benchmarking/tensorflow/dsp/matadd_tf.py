####### import statements ########
import tensorflow as tf


def matadd_tf(matA, matB, m, n):
    return (matA[:m][:, 0:n]) + (matB[:m][:, 0:n])


def matadd_tf_glued(matA, matB, m, n):
    matA = tf.convert_to_tensor(matA, dtype=tf.int32)
    matB = tf.convert_to_tensor(matB, dtype=tf.int32)
    return matadd_tf(matA, matB, m, n)


import os

####### more import statements for benchmarking ########
import time

import cv2
import numpy as np

####### setup for benchmarking ########
gpus = tf.config.list_physical_devices("GPU")
if not gpus:
    print("No GPU is available")
rng = np.random.default_rng(1)

folder = "./data/"

img_files = [
    os.path.join(folder, f)
    for f in os.listdir(folder)
    if os.path.isfile(os.path.join(folder, f))
]

bases = []
actives = []

for _file in img_files:
    img = cv2.imread(_file, cv2.IMREAD_GRAYSCALE).astype(np.uint8)
    rnd = (rng.random(img.shape, dtype=np.float32) * 255).astype(np.uint8)
    bases.append(img)
    actives.append(rnd)

####### runner. need to manually update for each file ########
runs = 10
times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(bases)):
        b = bases[i].astype(np.int32)
        a = actives[i].astype(np.int32)

        with tf.device("/CPU:0"):
            b = tf.convert_to_tensor(b, np.int32)
            a = tf.convert_to_tensor(a, np.int32)

            m, n = b.shape

        with tf.device("/GPU:0"):
            start_time = time.perf_counter()

            b = tf.identity(b)
            a = tf.identity(a)
            res = matadd_tf(b, a, m, n)
        with tf.device("/CPU:0"):
            res = tf.identity(res)
            end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("matadd_tf")
print(f"{np.average(times)} {np.std(times)}")

times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(bases)):
        b = bases[i].astype(np.int32)
        a = actives[i].astype(np.int32)

        with tf.device("/GPU:0"):
            b = tf.convert_to_tensor(b, np.int32)
            a = tf.convert_to_tensor(a, np.int32)
            m, n = b.shape

            start_time = time.perf_counter()
            matadd_tf(b, a, m, n)

            end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print(f"{np.average(times)} {np.std(times)}")
