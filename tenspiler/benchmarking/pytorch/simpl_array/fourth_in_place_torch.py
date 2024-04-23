####### import statements ########
import torch


def fourth_in_place_torch(arr, n):
    return ((arr[:n]) * (arr[:n])) * ((arr[:n]) * (arr[:n]))


def fourth_in_place_torch_glued(arr, n):
    arr = torch.tensor(arr, dtype=torch.int32)
    return fourth_in_place_torch(arr, n)


import os

####### more import statements for benchmarking ########
import time

import cv2
import numpy as np

####### setup for benchmarking ########
rng = np.random.default_rng(1)
if not torch.cuda.is_available():
    print("CUDA is not available on this system")
device = "cuda" if torch.cuda.is_available() else "cpu"
cpu = "cpu"

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
        b = bases[i].flatten().astype(np.int32)

        b = torch.from_numpy(b).to(dtype=torch.int32).to(cpu)

        (n,) = b.shape

        start_time = time.perf_counter()

        b = b.to(device)
        res = fourth_in_place_torch(b, n)
        res = res.to(cpu)

        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("fourth_in_place_torch")
print(f"{np.average(times)} {np.std(times)}")

times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(bases)):
        b = bases[i].flatten().astype(np.int32)

        b = torch.from_numpy(b).to(dtype=torch.int32).to(cpu)

        (n,) = b.shape

        b = b.to(device)
        start_time = time.perf_counter()
        res = fourth_in_place_torch(b, n)
        end_time = time.perf_counter()
        res = res.to(cpu)

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print(f"{np.average(times)} {np.std(times)}")
