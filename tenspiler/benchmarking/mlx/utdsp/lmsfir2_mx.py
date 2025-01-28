####### import statements ########
import mlx.core as mx


def lmsfir2_mx(NTAPS, input, coefficient, error):
    return (coefficient[: (NTAPS) - (1)]) + ((error) * (input[: (NTAPS) - (1)]))


def lmsfir2_mx_glued(NTAPS, input, coefficient, error):
    input = mx.array(input, mx.int32)
    coefficient = mx.array(coefficient, mx.int32)
    return lmsfir2_mx(NTAPS, input, coefficient, error)


import os
import time

import cv2

####### more import statements for benchmarking ########
import numpy as np

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
        b = mx.array(b, mx.int32)
        a = mx.array(a, mx.int32)
        (n,) = b.shape
        v = int(rng.integers(low=0, high=np.iinfo(np.int32).max + 1))

        start_time = time.perf_counter()
        mx.eval(lmsfir2_mx(n, b, a, v))

        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("lmsfir2_mx")
print(f"{np.average(times)} {np.std(times)}")
print(f"{np.average(times)} {np.std(times)}")
