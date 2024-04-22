
####### import statements ########
import numpy as np

def matrix_add_matrix_np (from_matrix, to_matrix):
    return (to_matrix) + (from_matrix)

def matrix_add_matrix_np_glued (from_matrix, to_matrix):
    from_matrix = np.array(from_matrix).astype(np.int32)
    to_matrix = np.array(to_matrix).astype(np.int32)
    return matrix_add_matrix_np(from_matrix, to_matrix)

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
        a = actives[i].astype(np.int32)
        start_time = time.perf_counter()
        matrix_add_matrix_np(b, a)

        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)   

print("matrix_add_matrix_np")
print(f"{np.average(times)} {np.std(times)}") 
print(f"{np.average(times)} {np.std(times)}") 
