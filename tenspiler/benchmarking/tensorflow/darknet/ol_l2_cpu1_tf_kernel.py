
####### import statements ########
import tensorflow as tf

def ol_l2_cpu1_tf(n, pred, truth):
    return ((pred[:n]) - (truth[:n])) * ((pred[:n]) - (truth[:n]))

def ol_l2_cpu1_tf_glued(n, pred, truth):
    pred = tf.convert_to_tensor(pred, dtype=tf.int32)
    truth = tf.convert_to_tensor(truth, dtype=tf.int32)
    return ol_l2_cpu1_tf(n, pred, truth)

####### more import statements for benchmarking ########
import time
import cv2
import os
import numpy as np

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
        b = bases[i].flatten().astype(np.int32)
        a = actives[i].flatten().astype(np.int32)
        
        with tf.device('/GPU:0'):
            b = tf.convert_to_tensor(b, np.int32)
            a = tf.convert_to_tensor(a, np.int32)
            
            n, = b.shape
            
            start_time = time.perf_counter()
            ol_l2_cpu1_tf(n, b, a)
            
            end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)   

print("ol_l2_cpu1_tf_kernel")
print(f"{np.average(times)} {np.std(times)}") 
