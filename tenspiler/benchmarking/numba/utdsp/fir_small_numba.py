####### import statements ########
import numpy as np
from numba import cuda


@cuda.jit()
def fir_small_numba(NTAPS, input, coefficient, res):
    sum = 0
    for i in range(NTAPS):
        sum += (coefficient[i]) * (input[i])
    res[0] = sum


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
b = bases[-1].flatten().astype(np.int32)
a = actives[-1].flatten().astype(np.int32)
res = np.array([0], dtype=np.int32)

threadsperblock = 32
blockspergrid = (b.size + (threadsperblock - 1)) // threadsperblock

(n,) = b.shape

fir_small_numba[blockspergrid, threadsperblock](n, b, a, res)

runs = 10
times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(bases)):
        b = bases[i].flatten().astype(np.int32)
        a = actives[i].flatten().astype(np.int32)
        res = np.array([0], dtype=np.int32)

        threadsperblock = 32
        blockspergrid = (b.size + (threadsperblock - 1)) // threadsperblock

        (n,) = b.shape

        start_time = time.perf_counter()
        fir_small_numba[blockspergrid, threadsperblock](n, b, a, res)

        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("fir_small_numba")
print(f"{np.average(times)} {np.std(times)}")
print(f"{np.average(times)} {np.std(times)}")
