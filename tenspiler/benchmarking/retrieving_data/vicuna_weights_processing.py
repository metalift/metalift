from transformers import AutoTokenizer, AutoModelForCausalLM
import h5py
model33b = AutoModelForCausalLM.from_pretrained("lmsys/vicuna-33b-v1.3")

model33b.save_pretrained("<some_location>", safe_serialization=True, max_shard_size="100GB")

weights33b = model33b.state_dict()
with h5py.File('./vicuna_weight_full.h5', 'w') as h5f:
    for k, v in weights33b.items():
        h5f.create_dataset(k, data=v.cpu().numpy())
    print(len(weights33b))
print("Weights for vicuna 33B are saved")

model7b = AutoModelForCausalLM.from_pretrained("lmsys/vicuna-7b-v1.5")

model7b.save_pretrained("<some_location>", safe_serialization=True, max_shard_size="100GB")

weights7b = model7b.state_dict()
with h5py.File('./vicuna_weight7b_full.h5', 'w') as h5f:
    for k, v in weights7b.items():
        h5f.create_dataset(k, data=v.cpu().numpy())
    print(len(weights7b))
print("Weights for vicuna 7B are saved")