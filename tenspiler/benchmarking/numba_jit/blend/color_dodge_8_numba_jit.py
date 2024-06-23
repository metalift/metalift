####### import statements ########
import numpy as np
from numba import jit, cuda

@jit(nopython=True)
def color_dodge_8_numba_jit(base, active):
#   output = []
  m = len(base)
  n = len(base[0])
  output = np.empty((m, n))
  for i in range(m):
    # curr_row = []
    for j in range(n):
      if active[i][j] == 255:
        pixel = 255
      else:
        pixel = base[i][j] // (255 - active[i][j])
      output[i][j] = pixel
    #   curr_row.append(pixel)
    # output.append(curr_row)
  return output

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
b = bases[-1]
a = actives[-1]



color_dodge_8_numba_jit(b, a)


runs = 10
times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(bases)):
        b = bases[i]
        a = actives[i]
        
        

        start_time = time.perf_counter()
        color_dodge_8_numba_jit(b, a)
        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("color_dodge_8_numba_jit")
print(f"{np.average(times)} {np.std(times)}")
print(f"{np.average(times)} {np.std(times)}")
