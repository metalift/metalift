####### import statements ########
import mlx.core as mx


def dissolve_blend_8_mx(base, active, opacity, rand_cons):
    return mx.where(
        (opacity) - ((((rand_cons) % (100)) + (1)) // (100)) >= 0, active, base
    )


def dissolve_blend_8_mx_glued(base, active, opacity, rand_cons):
    base = mx.array(base, mx.uint8)
    active = mx.array(active, mx.uint8)
    return dissolve_blend_8_mx(base, active, opacity, rand_cons)


import os
import time

import cv2

####### more import statements for benchmarking ########
import numpy as np

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
        base = bases[i]
        active = actives[i]
        b = mx.array(base, mx.uint8)
        a = mx.array(active, mx.uint8)
        opacity = float(rng.random(dtype=np.float32))
        rand_cons = int(rng.integers(low=0, high=256))
        start_time = time.perf_counter()
        mx.eval(dissolve_blend_8_mx(b, a, opacity, rand_cons))
        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("dissolve_blend_8_mx")
print(f"{np.average(times)} {np.std(times)}")
print(f"{np.average(times)} {np.std(times)}")
