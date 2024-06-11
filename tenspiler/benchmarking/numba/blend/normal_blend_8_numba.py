####### import statements ########
import numpy as np
from numba import jit, cuda

@cuda.jit()
def normal_blend_8_numba(base, active, opacity):
#   output = []
  for i in range(len(base)):
    temp = opacity * active[i] + (255 - opacity) * base[i]
    # output.append(opacity * active[i] + (255 - opacity) * base[i])
#   return output

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
b = bases[-1].flatten()
a = actives[-1].flatten()
opacity = int(rng.integers(low=0, high=256))
threadsperblock = 32
blockspergrid = (b.size + (threadsperblock - 1)) // threadsperblock

normal_blend_8_numba[blockspergrid, threadsperblock](b, a, opacity)

runs = 10
times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(bases)):
        b = bases[i].flatten()
        a = actives[i].flatten()
        opacity = int(rng.integers(low=0, high=256))
        threadsperblock = 32
        blockspergrid = (b.size + (threadsperblock - 1)) // threadsperblock

        start_time = time.perf_counter()
        normal_blend_8_numba[blockspergrid, threadsperblock](b, a, opacity)
        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("normal_blend_8_numba")
print(f"{np.average(times)} {np.std(times)}")
print(f"{np.average(times)} {np.std(times)}")
