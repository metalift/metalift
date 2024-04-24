####### import statements ########
import mlx.core as mx


def mat1x3_mx(N, h, x):
    return mx.matmul(h[:N][:, 0:N], x[:N])


def mat1x3_mx_glued(N, h, x):
    h = mx.array(h, mx.float32)
    x = mx.array(x, mx.float32)
    return mat1x3_mx(N, h, x)


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
        # matmul requires float
        a = actives[i].flatten().astype(np.float32)
        b = bases[i].astype(np.float32)
        b = mx.array(b, mx.float32)
        a = mx.array(a, mx.float32)
        m, n = b.shape
        if m < n:
            n = m

        start_time = time.perf_counter()
        mx.eval(mat1x3_mx(n, b, a))

        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("mat1x3_mx")
print(f"{np.average(times)} {np.std(times)}")
print(f"{np.average(times)} {np.std(times)}")
