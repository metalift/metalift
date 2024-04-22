
####### import statements ########
import tensorflow as tf

def mult_add_into_cpu_tf(N, X, Y, Z):
    return (Z[:N]) + ((X[:N]) * (Y[:N]))

def mult_add_into_cpu_tf_glued(N, X, Y, Z):
    X = tf.convert_to_tensor(X, dtype=tf.int32)
    Y = tf.convert_to_tensor(Y, dtype=tf.int32)
    Z = tf.convert_to_tensor(Z, dtype=tf.int32)
    return mult_add_into_cpu_tf(N, X, Y, Z)

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
        b = bases[i].flatten().astype(np.int32)
        a = actives[i].flatten().astype(np.int32)
        rand_f = rng.integers(low=0, high=np.iinfo(np.int32).max + 1, size=b.shape, dtype=np.int32)
        
        with tf.device('/CPU:0'):
            b = tf.convert_to_tensor(b, np.int32)
            a = tf.convert_to_tensor(a, np.int32)
            rand_f = tf.convert_to_tensor(rand_f, np.int32)

            n, = b.shape
            
        with tf.device('/GPU:0'):
            start_time = time.perf_counter()

            b = tf.identity(b)
            a = tf.identity(a)
            rand_f = tf.identity(rand_f)
            res = mult_add_into_cpu_tf(n, b, a, rand_f)
        with tf.device('/CPU:0'):
            res = tf.identity(res)
            end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)   

print("mult_add_into_cpu_tf")
print(f"{np.average(times)} {np.std(times)}") 

times = []
for _ in range(runs):
    total_time = 0
    for i in range(len(bases)):
        b = bases[i].flatten().astype(np.int32)
        a = actives[i].flatten().astype(np.int32)
        rand_f = rng.integers(low=0, high=np.iinfo(np.int32).max + 1, size=b.shape, dtype=np.int32)
        
        with tf.device('/GPU:0'):
            b = tf.convert_to_tensor(b, np.int32)
            a = tf.convert_to_tensor(a, np.int32)
            rand_f = tf.convert_to_tensor(rand_f, np.int32)

            n, = b.shape
            
            start_time = time.perf_counter()
            mult_add_into_cpu_tf(n, b, a, rand_f)
            
            end_time = time.perf_counter()

        total_time += (end_time - start_time) * 1000

    times.append(total_time)

times = np.array(times)   

print(f"{np.average(times)} {np.std(times)}") 
