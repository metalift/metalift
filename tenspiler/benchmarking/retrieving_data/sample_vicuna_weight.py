import h5py
import numpy as np

def sample(src, dest, sampling_rate=0.005):
    """ Recursively copy the structure of the HDF5 file and sample data. """
    for name, item in src.items():
        if isinstance(item, h5py.Dataset):
            # Perform sampling
            data = item[()]
            if data.size > 1: 
                sample_size = max(1, int(data.shape[0] * sampling_rate)) 
                indices = np.random.choice(data.shape[0], sample_size, replace=False)
                sampled_data = data[indices]
            else:
                sampled_data = data 

            dset = dest.create_dataset(name, data=sampled_data, dtype=item.dtype, compression="gzip")
            for k, v in item.attrs.items():
                dset.attrs[k] = v

        elif isinstance(item, h5py.Group):
            group = dest.create_group(name)
            for k, v in item.attrs.items():
                group.attrs[k] = v
            sample(item, group, sampling_rate)

np.random.seed(1)

original_weights_path = './vicuna_weight.h5'
sampled_weights_path = './vicuna_weight_sampled.h5'

with h5py.File(original_weights_path, 'r') as original_file, \
     h5py.File(sampled_weights_path, 'w') as new_file:
    sample(original_file, new_file, 0.005)

original_weights_path = './vicuna_weight7b.h5'
sampled_weights_path = './vicuna_weight7b_sampled.h5'

with h5py.File(original_weights_path, 'r') as original_file, \
     h5py.File(sampled_weights_path, 'w') as new_file:
    sample(original_file, new_file, 0.01)
