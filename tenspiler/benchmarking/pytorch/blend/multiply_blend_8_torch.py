####### import statements ########
import torch


def multiply_blend_8_torch(base, active):
    return ((base) * (active)) // (255)


def multiply_blend_8_torch_glued(base, active):
    base = torch.tensor(base, dtype=torch.uint8)
    active = torch.tensor(active, dtype=torch.uint8)
    return multiply_blend_8_torch(base, active)


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
        b = torch.from_numpy(bases[i]).to(dtype=torch.uint8).to(cpu)
        a = torch.from_numpy(actives[i]).to(dtype=torch.uint8).to(cpu)

        start_time = time.perf_counter()
        b = b.to(device)
        a = a.to(device)
        res = multiply_blend_8_torch(b, a)
        res = res.to(cpu)
        end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)

print("multiply_blend_8_torch")
print(f"{np.average(times)} {np.std(times)}")

times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(bases)):
        b = torch.from_numpy(bases[i]).to(dtype=torch.uint8).to(device)
        a = torch.from_numpy(actives[i]).to(dtype=torch.uint8).to(device)
        start_time = time.perf_counter()
        multiply_blend_8_torch(b, a)
        end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)
print(f"{np.average(times)} {np.std(times)}")
