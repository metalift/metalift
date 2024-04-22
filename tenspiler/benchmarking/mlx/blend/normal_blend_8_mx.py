
####### import statements ########
import mlx.core as mx

def normal_blend_8_mx (base, active, opacity):
    return ((opacity) * (active)) + (((255) - (opacity)) * (base))

def normal_blend_8_mx_glued (base, active, opacity):
    base = mx.array(base, mx.uint8)
    active = mx.array(active, mx.uint8)
    return normal_blend_8_mx(base, active, opacity)


####### more import statements for benchmarking ########
import numpy as np
import time
import cv2
import os

####### setup for benchmarking ########
rng = np.random.default_rng(1)

folder = "./data/"

img_files = [os.path.join(folder, f) for f in os.listdir(folder) if os.path.isfile(os.path.join(folder, f))]

bases = []
actives = []

for _file in img_files:
    img = cv2.imread(_file, cv2.IMREAD_GRAYSCALE).astype(np.uint8)
    rnd = (rng.random(img.shape, dtype = np.float32) * 255).astype(np.uint8)
    bases.append(img)
    actives.append(rnd)

####### runner. need to manually update for each file ########  
runs = 10
times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(bases)):
        base = bases[i].flatten()
        active = actives[i].flatten()
        b = mx.array(base, mx.uint8)
        a = mx.array(active, mx.uint8)
        opacity = int(rng.integers(low=0, high=256))
        start_time = time.perf_counter()
        mx.eval(normal_blend_8_mx(b, a, opacity))
        end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)   

print("normal_blend_8_mx")
print(f"{np.average(times)} {np.std(times)}") 
print(f"{np.average(times)} {np.std(times)}") 
