####### import statements ########
import torch


def normal_blend_f_torch(base, active, opacity):
    return ((opacity) * (active)) + (((1) - (opacity)) * (base))


def normal_blend_f_torch_glued(base, active, opacity):
    base = torch.tensor(base, dtype=torch.float32)
    active = torch.tensor(active, dtype=torch.float32)
    return normal_blend_f_torch(base, active, opacity)


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
        base = bases[i].flatten().astype(np.float32)
        active = actives[i].flatten().astype(np.float32)
        b = torch.from_numpy(base).to(dtype=torch.float32).to(cpu)
        a = torch.from_numpy(active).to(dtype=torch.float32).to(cpu)
        opacity = float(rng.random(dtype=np.float32))

        start_time = time.perf_counter()
        b = b.to(device)
        a = a.to(device)

        res = normal_blend_f_torch(b, a, opacity)
        res = res.to(cpu)
        end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("normal_blend_f_torch")
print(f"{np.average(times)} {np.std(times)}")

times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(bases)):
        base = bases[i].flatten().astype(np.float32)
        active = actives[i].flatten().astype(np.float32)
        b = torch.from_numpy(base).to(dtype=torch.float32).to(device)
        a = torch.from_numpy(active).to(dtype=torch.float32).to(device)
        opacity = float(rng.random(dtype=np.float32))

        start_time = time.perf_counter()
        normal_blend_f_torch(b, a, opacity)
        end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)
print(f"{np.average(times)} {np.std(times)}")
