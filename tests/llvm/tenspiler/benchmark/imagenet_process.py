import os
import os.path
import tarfile

import numpy as np
import torchvision

if __name__ == "__main__":
    root = "."
    output_folder = "./data/"
    tarfile_name = "data.tar.gz"
    size = 10000

    if not os.path.exists(output_folder):
        os.makedirs(output_folder)

    image_set = torchvision.datasets.ImageNet(root=root)

    np.random.seed(1)
    rng = np.random.default_rng()
    chosen = rng.choice(len(image_set), size, replace=False)
    for i in chosen:
        img, _ = image_set[i]
        img.save(f"{output_folder}{i}.jpeg", "JPEG")

    with tarfile.open(tarfile_name, "w:gz") as tar:
        tar.add(output_folder, arcname=os.path.basename(output_folder))
