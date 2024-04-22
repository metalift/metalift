
####### import statements ########
import mlx.core as mx

def ol_l2_cpu1_mx (n, pred, truth):
    return ((pred[:n]) - (truth[:n])) * ((pred[:n]) - (truth[:n]))

def ol_l2_cpu1_mx_glued (n, pred, truth):
    pred = mx.array(pred, mx.int32)
    truth = mx.array(truth, mx.int32)
    return ol_l2_cpu1_mx(n, pred, truth)

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
        b = bases[i].flatten().astype(np.int32)
        a = actives[i].flatten().astype(np.int32)
        b = mx.array(b, mx.int32)
        a = mx.array(a, mx.int32)
        n, = b.shape

        start_time = time.perf_counter()
        mx.eval(ol_l2_cpu1_mx(n, b, a))

        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)   

print("ol_l2_cpu1_mx")
print(f"{np.average(times)} {np.std(times)}") 
print(f"{np.average(times)} {np.std(times)}") 
