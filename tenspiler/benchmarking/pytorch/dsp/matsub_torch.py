
####### import statements ########
import torch

def matsub_torch (matA, matB, m, n):
    return (matA[:m][:, 0:n]) - (matB[:m][:, 0:n])

def matsub_torch_glued (matA, matB, m, n):
    matA = torch.tensor(matA, dtype=torch.int32)
    matB = torch.tensor(matB, dtype=torch.int32)
    return matsub_torch(matA, matB, m, n)

####### more import statements for benchmarking ########
import time
import cv2
import os
import numpy as np

####### setup for benchmarking ########
rng = np.random.default_rng(1)
device = 'cuda' if torch.cuda.is_available() else 'cpu'
cpu = 'cpu'

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

        b = torch.from_numpy(b).to(dtype=torch.int32).to(cpu)
        a = torch.from_numpy(a).to(dtype=torch.int32).to(cpu)
      
        m, n = b.shape
        
        start_time = time.perf_counter()

        b = b.to(device)
        a = a.to(device)
        res = matsub_torch(b, a, m, n)
        res = res.to(cpu)
        
        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)   

print("matsub_torch")
print(f"{np.average(times)} {np.std(times)}") 
