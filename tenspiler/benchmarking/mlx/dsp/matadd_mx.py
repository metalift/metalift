####### import statements ########
import mlx.core as mx


def matadd_mx(matA, matB, m, n):
    return (matA[:m][:, 0:n]) + (matB[:m][:, 0:n])


def matadd_mx_glued(matA, matB, m, n):
    matA = mx.array(matA, mx.int32)
    matB = mx.array(matB, mx.int32)
    return matadd_mx(matA, matB, m, n)


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
        b = bases[i].astype(np.int32)
        a = actives[i].astype(np.int32)
        b = mx.array(b, mx.int32)
        a = mx.array(a, mx.int32)
        m, n = b.shape

        start_time = time.perf_counter()
        mx.eval(matadd_mx(b, a, m, n))

        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("matadd_mx")
print(f"{np.average(times)} {np.std(times)}")
print(f"{np.average(times)} {np.std(times)}")
