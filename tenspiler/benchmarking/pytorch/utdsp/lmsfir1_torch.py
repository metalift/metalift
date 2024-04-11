
####### import statements ########
import torch

def lmsfir1_torch (NTAPS, input, coefficient):
    return torch.sum((coefficient[:NTAPS]) * (input[:NTAPS]))

def lmsfir1_torch_glued (NTAPS, input, coefficient):
    input = torch.tensor(input, dtype=torch.int32)
    coefficient = torch.tensor(coefficient, dtype=torch.int32)
    return lmsfir1_torch(NTAPS, input, coefficient)

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
    
        b = bases[i].flatten().astype(np.int32)
        a = actives[i].flatten().astype(np.int32)
       
        b = torch.from_numpy(b).to(dtype=torch.int32).to(cpu)
        a = torch.from_numpy(a).to(dtype=torch.int32).to(cpu)
        
        n, = b.shape
        
        start_time = time.perf_counter()

        b = b.to(device)
        a = a.to(device)
        res = lmsfir1_torch(n, b, a)
        res = res.to(cpu)
        

        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)   

print("lmsfir1_torch")
print(f"{np.average(times)} {np.std(times)}") 
