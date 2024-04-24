####### import statements ########
import mlx.core as mx


def mult_add_into_cpu_mx(N, X, Y, Z):
    return (Z[:N]) + ((X[:N]) * (Y[:N]))


def mult_add_into_cpu_mx_glued(N, X, Y, Z):
    X = mx.array(X, mx.int32)
    Y = mx.array(Y, mx.int32)
    Z = mx.array(Z, mx.int32)
    return mult_add_into_cpu_mx(N, X, Y, Z)


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

        rand_f = rng.integers(
            low=0, high=np.iinfo(np.int32).max + 1, size=b.shape, dtype=np.int32
        )
        b = mx.array(b, mx.int32)
        a = mx.array(a, mx.int32)
        rand_f = mx.array(rand_f, mx.int32)

        (n,) = b.shape
        start_time = time.perf_counter()
        mx.eval(mult_add_into_cpu_mx(n, b, a, rand_f))

        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("mult_add_into_cpu_mx")
print(f"{np.average(times)} {np.std(times)}")
print(f"{np.average(times)} {np.std(times)}")
