####### import statements ########
import numpy as np


def mat1x3_np(N, h, x):
    return np.matmul(h[:N][:, 0:N], x[:N])


def mat1x3_np_glued(N, h, x):
    h = np.array(h).astype(np.int32)
    x = np.array(x).astype(np.int32)
    return mat1x3_np(N, h, x)


import os

####### more import statements for benchmarking ########
import time

import cv2

####### setup for benchmarking ########
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
        a = actives[i].flatten().astype(np.int32)
        b = bases[i].astype(np.int32)
        m, n = b.shape
        if m < n:
            n = m

        start_time = time.perf_counter()
        mat1x3_np(n, b, a)

        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("mat1x3_np")
print(f"{np.average(times)} {np.std(times)}")
print(f"{np.average(times)} {np.std(times)}")
