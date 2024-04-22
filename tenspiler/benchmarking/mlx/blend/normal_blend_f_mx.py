
####### import statements ########
import mlx.core as mx

def normal_blend_f_mx (base, active, opacity):
    return ((opacity) * (active)) + (((1) - (opacity)) * (base))

def normal_blend_f_mx_glued (base, active, opacity):
    base = mx.array(base, mx.float32)
    active = mx.array(active, mx.float32)
    return normal_blend_f_mx(base, active, opacity)


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
        base = bases[i].flatten().astype(np.float32)
        active = actives[i].flatten().astype(np.float32)
        b = mx.array(base, mx.float32)
        a = mx.array(active, mx.float32)
        opacity = float(rng.random(dtype = np.float32))
        start_time = time.perf_counter()
        mx.eval(normal_blend_f_mx(b, a, opacity))
        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000


    times.append(total_time)

times = np.array(times)   

print("normal_blend_f_mx")
print(f"{np.average(times)} {np.std(times)}") 
print(f"{np.average(times)} {np.std(times)}") 
