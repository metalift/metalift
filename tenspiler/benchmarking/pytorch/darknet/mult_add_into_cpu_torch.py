####### import statements ########
import torch


def mult_add_into_cpu_torch(N, X, Y, Z):
    return (Z[:N]) + ((X[:N]) * (Y[:N]))


def mult_add_into_cpu_torch_glued(N, X, Y, Z):
    X = torch.tensor(X, dtype=torch.int32)
    Y = torch.tensor(Y, dtype=torch.int32)
    Z = torch.tensor(Z, dtype=torch.int32)
    return mult_add_into_cpu_torch(N, X, Y, Z)


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
runs = 10
times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(bases)):
        b = bases[i].flatten().astype(np.int32)
        a = actives[i].flatten().astype(np.int32)
        rand_f = rng.integers(
            low=0, high=np.iinfo(np.int32).max + 1, size=b.shape, dtype=np.int32
        )

        b = torch.from_numpy(b).to(dtype=torch.int32).to(cpu)
        a = torch.from_numpy(a).to(dtype=torch.int32).to(cpu)
        rand_f = torch.from_numpy(rand_f).to(dtype=torch.int32).to(cpu)

        (n,) = b.shape

        start_time = time.perf_counter()

        b = b.to(device)
        a = a.to(device)
        rand_f = rand_f.to(device)

        res = mult_add_into_cpu_torch(n, b, a, rand_f)
        res = res.to(cpu)

        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("mult_add_into_cpu_torch")
print(f"{np.average(times)} {np.std(times)}")

times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(bases)):
        b = bases[i].flatten().astype(np.int32)
        a = actives[i].flatten().astype(np.int32)
        rand_f = rng.integers(
            low=0, high=np.iinfo(np.int32).max + 1, size=b.shape, dtype=np.int32
        )

        b = torch.from_numpy(b).to(dtype=torch.int32).to(cpu)
        a = torch.from_numpy(a).to(dtype=torch.int32).to(cpu)
        rand_f = torch.from_numpy(rand_f).to(dtype=torch.int32).to(cpu)

        (n,) = b.shape

        b = b.to(device)
        a = a.to(device)
        rand_f = rand_f.to(device)

        start_time = time.perf_counter()
        res = mult_add_into_cpu_torch(n, b, a, rand_f)
        end_time = time.perf_counter()
        res = res.to(cpu)

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)
print(f"{np.average(times)} {np.std(times)}")
