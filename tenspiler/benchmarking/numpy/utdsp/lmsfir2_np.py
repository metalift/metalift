
####### import statements ########
import numpy as np

def lmsfir2_np (NTAPS, input, coefficient, error):
    return (coefficient[:(NTAPS) - (1)]) + ((error) * (input[:(NTAPS) - (1)]))

def lmsfir2_np_glued (NTAPS, input, coefficient, error):
    input = np.array(input).astype(np.int32)
    coefficient = np.array(coefficient).astype(np.int32)
    return lmsfir2_np(NTAPS, input, coefficient, error)

####### more import statements for benchmarking ########
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
        n, = b.shape
        v = rng.integers(low=0, high=np.iinfo(np.int32).max + 1)

        start_time = time.perf_counter()
        lmsfir2_np(n, b, a, v)

        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)   

print("lmsfir2_np")
print(f"{np.average(times)} {np.std(times)}") 
