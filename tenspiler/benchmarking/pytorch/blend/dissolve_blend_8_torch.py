####### import statements ########
import torch


def dissolve_blend_8_torch(base, active, opacity, rand_cons):
    return torch.where(
        torch.tensor((opacity) - ((((rand_cons) % (100)) + (1)) // (100)) >= 0),
        active,
        base,
    )


def dissolve_blend_8_torch_glued(base, active, opacity, rand_cons):
    base = torch.tensor(base, dtype=torch.uint8)
    active = torch.tensor(active, dtype=torch.uint8)
    return dissolve_blend_8_torch(base, active, opacity, rand_cons)


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
        base = bases[i]
        active = actives[i]
        b = torch.from_numpy(base).to(dtype=torch.uint8).to(cpu)
        a = torch.from_numpy(active).to(dtype=torch.uint8).to(cpu)
        opacity = float(rng.random(dtype=np.float32))
        rand_cons = int(rng.integers(low=0, high=256))

        start_time = time.perf_counter()
        b = b.to(device)
        a = a.to(device)
        res = dissolve_blend_8_torch(b, a, opacity, rand_cons)
        res = res.to(cpu)
        end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("dissolve_blend_8_torch")
print(f"{np.average(times)} {np.std(times)}")

times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(bases)):
        base = bases[i]
        active = actives[i]
        b = torch.from_numpy(base).to(dtype=torch.uint8).to(device)
        a = torch.from_numpy(active).to(dtype=torch.uint8).to(device)
        opacity = float(rng.random(dtype=np.float32))
        rand_cons = int(rng.integers(low=0, high=256))
        start_time = time.perf_counter()
        dissolve_blend_8_torch(b, a, opacity, rand_cons)
        end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)
print(f"{np.average(times)} {np.std(times)}")
