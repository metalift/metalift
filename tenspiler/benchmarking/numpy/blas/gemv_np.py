
####### import statements ########
import numpy as np

def gemv_np (M, N, A, x):
    return np.matmul(A[:M][:, 0:N], x[:N])

def gemv_np_glued (M, N, A, x):
    A = np.array(A).astype(np.int32)
    x = np.array(x).astype(np.int32)
    return gemv_np(M, N, A, x)

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
        b = bases[i].astype(np.int32)
        M, N = b.shape
        a = actives[i].flatten().astype(np.int32)[:N]

        start_time = time.perf_counter()
        gemv_np(M, N, b, a)

        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)   

print("gemv_np")
print(f"{np.average(times)} {np.std(times)}") 
print(f"{np.average(times)} {np.std(times)}") 
