#!/usr/bin/env python
# coding: utf-8

# In[1]:


import os
import time

import cv2
import numpy as np
from numba import njit

# In[2]:


rng = np.random.default_rng(1)


# In[3]:


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


# In[5]:


def mat_runner(bases, actives, f):
    total_time = 0
    for i in range(len(bases)):
        b = bases[i]
        a = actives[i]
        start_time = time.perf_counter()
        f(b, a)
        end_time = time.perf_counter()
        del a
        del b
        total_time += (end_time - start_time) * 1000
    return total_time


def vec_runner_int(bases, actives, f):
    total_time = 0
    for i in range(len(bases)):
        b = bases[i].flatten()
        a = actives[i].flatten()
        opacity = rng.random(1, dtype=np.float32).astype(np.uint8)
        start_time = time.perf_counter()
        f(b, a, opacity)
        end_time = time.perf_counter()
        del a
        del b
        total_time += (end_time - start_time) * 1000
    return total_time


def vec_runner_float(bases, actives, f):
    total_time = 0
    for i in range(len(bases)):
        b = bases[i].flatten().astype(np.float32)
        a = actives[i].flatten().astype(np.float32)
        opacity = rng.random(1, dtype=np.float32)
        start_time = time.perf_counter()
        f(b, a, opacity)
        end_time = time.perf_counter()
        del a
        del b
        total_time += (end_time - start_time) * 1000
    return total_time


def timer(input1, input2, f, runner):
    runs = 10
    times = []
    for i in range(runs):
        if i == 0:
            print("first run, skipping")
            continue
        print(f"{i}th run ------")
        times.append(runner(input1, input2, f))
        times_seen_so_far = np.array(times)
        print(f"{f.__name__}")
        print(f"{np.average(times_seen_so_far)}ms +/- {np.std(times_seen_so_far)}ms")


# In[16]:


# @njit
def normal_blend_f_np(base, active, opacity):
    return opacity * active + (1 - opacity) * base


# In[27]:


timer(bases, actives, normal_blend_f_np, vec_runner_float)


# In[6]:


np.random.seed(0)


def mat_runner_float(bases, actives, f):
    total_time = 0
    for i in range(len(bases)):
        b = bases[i].astype(np.float32)
        a = actives[i].astype(np.float32)
        opacity = rng.random(1, dtype=np.float32)
        start_time = time.perf_counter()
        f(b, a, opacity)
        end_time = time.perf_counter()
        del a
        del b
        total_time += (end_time - start_time) * 1000
    return total_time


# In[9]:


@njit
def dissolve_blend_8_np(base, active, opacity):
    return np.where(
        np.greater_equal(
            opacity - ((np.random.randint(1, 2147483647, base.shape) % 100) + 1) / 100,
            0,
        ),
        active,
        base,
    )


# In[10]:


timer(bases, actives, dissolve_blend_8_np, mat_runner_float)
