####### import statements ########
import numpy as np


def normal_blend_f_np(base, active, opacity):
    return ((opacity) * (active)) + (((1) - (opacity)) * (base))


def normal_blend_f_np_glued(base, active, opacity):
    base = np.array(base).astype(np.float32)
    active = np.array(active).astype(np.float32)
    return normal_blend_f_np(base, active, opacity)


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
        b = bases[i].flatten().astype(np.float32)
        a = actives[i].flatten().astype(np.float32)
        opacity = float(rng.random(dtype=np.float32))
        start_time = time.perf_counter()
        normal_blend_f_np(b, a, opacity)
        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("normal_blend_f_np")
print(f"{np.average(times)} {np.std(times)}")
print(f"{np.average(times)} {np.std(times)}")
