import os
import shutil

import numpy as np

source_directory = "./data_full/"
destination_directory = "./data_sampled"

size = 1000

if not os.path.exists(destination_directory):
    os.makedirs(destination_directory)

all_images = [
    file
    for file in os.listdir(source_directory)
    if file.endswith(".jpeg") or file.endswith(".jpg")
]

sampled_images = np.random.choice(all_images, size, replace=False)

for image in sampled_images:
    shutil.copy(
        os.path.join(source_directory, image),
        os.path.join(destination_directory, image),
    )
