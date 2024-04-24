####### import statements ########
import numpy as np


def fir_small_np(NTAPS, input, coefficient):
    return np.sum((coefficient[:NTAPS]) * (input[:NTAPS]))


def fir_small_np_glued(NTAPS, input, coefficient):
    input = np.array(input).astype(np.int32)
    coefficient = np.array(coefficient).astype(np.int32)
    return fir_small_np(NTAPS, input, coefficient)


import os

####### more import statements for benchmarking ########
import time

import cv2

####### setup for benchmarking ########
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
        b = bases[i].flatten().astype(np.int32)
        a = actives[i].flatten().astype(np.int32)

        (n,) = b.shape

        start_time = time.perf_counter()
        fir_small_np(n, b, a)

        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("fir_small_np")
print(f"{np.average(times)} {np.std(times)}")
print(f"{np.average(times)} {np.std(times)}")
