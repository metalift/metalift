
####### import statements ########
import numpy as np

def overlay_blend_8_np (base, active):
    return np.where(np.greater_equal(base, 128), ((((2) * (base)) + (base)) - ((((2) * (base)) * (base)) // (255))) - (255), (((2) * (base)) * (base)) // (255))

def overlay_blend_8_np_glued (base, active):
    base = np.array(base).astype(np.uint8)
    active = np.array(active).astype(np.uint8)
    return overlay_blend_8_np(base, active)


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
        b = bases[i]
        a = actives[i]
        start_time = time.perf_counter()
        overlay_blend_8_np(b, a)
        end_time = time.perf_counter()
        total_time += (end_time - start_time) * 1000


    times.append(total_time)

times = np.array(times)   

print("overlay_blend_8_np")
print(f"{np.average(times)} {np.std(times)}") 
print(f"{np.average(times)} {np.std(times)}") 