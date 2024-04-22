
####### import statements ########
import tensorflow as tf

def gemv_tf(M, N, A, x):
    return tf.linalg.matvec(A[:M][:, 0:N], x[:N])

def gemv_tf_glued(M, N, A, x):
    A = tf.convert_to_tensor(A, dtype=tf.int32)
    x = tf.convert_to_tensor(x, dtype=tf.int32)
    return gemv_tf(M, N, A, x)

####### more import statements for benchmarking ########
import time
import cv2
import os
import numpy as np

####### setup for benchmarking ########
gpus = tf.config.list_physical_devices('GPU')
if not gpus:
    print("No GPU is available")
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
        a = actives[i].flatten().astype(np.int32)
        b = bases[i].astype(np.int32)

        with tf.device('/CPU:0'):
            b = tf.convert_to_tensor(b, np.int32)
            a = tf.convert_to_tensor(a, np.int32)

            m, n = b.shape

            a = a[:n]
        with tf.device('/GPU:0'):
            start_time = time.perf_counter()

            b = tf.identity(b)
            a = tf.identity(a)
            res = gemv_tf(m, n, b, a)
        with tf.device('/CPU:0'):
            res = tf.identity(res)
            end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)   

print("gemv_tf")
print(f"{np.average(times)} {np.std(times)}") 

times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(bases)):
        a = actives[i].flatten().astype(np.int32)
        b = bases[i].astype(np.int32)
        
        with tf.device('/GPU:0'):
            b = tf.convert_to_tensor(b, np.int32)
            a = tf.convert_to_tensor(a, np.int32)
            
            m, n = b.shape
            a = a[:n]

            start_time = time.perf_counter()
            
            res = gemv_tf(m, n, b, a)
            end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)   

print(f"{np.average(times)} {np.std(times)}") 
