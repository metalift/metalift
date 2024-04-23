####### import statements ########
import tensorflow as tf


def dissolve_blend_8_tf(base, active, opacity, rand_cons):
    return tf.where(
        (opacity) - ((((rand_cons) % (100)) + (1)) // (100)) >= 0, active, base
    )


def dissolve_blend_8_tf_glued(base, active, opacity, rand_cons):
    base = tf.convert_to_tensor(base, dtype=tf.uint8)
    active = tf.convert_to_tensor(active, dtype=tf.uint8)
    return dissolve_blend_8_tf(base, active, opacity, rand_cons)


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

folder = "./tenspiler/data/data_sampled"

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
        base = bases[i].astype(np.float32)
        active = actives[i].astype(np.float32)
        with tf.device("/CPU:0"):
            b = tf.convert_to_tensor(base, np.float32)
            a = tf.convert_to_tensor(active, np.float32)
            opacity = float(rng.random(dtype=np.float32))
            rand_cons = int(rng.integers(low=0, high=256))
        with tf.device("/GPU:0"):
            start_time = time.perf_counter()
            b = tf.identity(b)
            a = tf.identity(a)

            res = dissolve_blend_8_tf(b, a, opacity, rand_cons)
        with tf.device("/CPU:0"):
            res = tf.identity(res)
            end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("dissolve_blend_8_tf")
print(f"{np.average(times)} {np.std(times)}")


times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(bases)):
        base = bases[i].astype(np.float32)
        active = actives[i].astype(np.float32)
        with tf.device("/GPU:0"):
            b = tf.convert_to_tensor(base, np.float32)
            a = tf.convert_to_tensor(active, np.float32)
            opacity = float(rng.random(dtype=np.float32))
            rand_cons = int(rng.integers(low=0, high=256))
            start_time = time.perf_counter()
            dissolve_blend_8_tf(b, a, opacity, rand_cons)
            end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print(f"{np.average(times)} {np.std(times)}")
