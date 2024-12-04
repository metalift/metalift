import h5py
from transformers import AutoModelForCausalLM

model33b = AutoModelForCausalLM.from_pretrained("lmsys/vicuna-33b-v1.3")

weights33b = model33b.state_dict()
with h5py.File("./vicuna_weight33b_full.h5", "w") as h5f:
    for k, v in weights33b.items():
        h5f.create_dataset(k, data=v.cpu().numpy())
    print(len(weights33b))
print("Weights for vicuna 33B are saved")

model7b = AutoModelForCausalLM.from_pretrained("lmsys/vicuna-7b-v1.5")

weights7b = model7b.state_dict()
with h5py.File("./vicuna_weight7b_full.h5", "w") as h5f:
    for k, v in weights7b.items():
        h5f.create_dataset(k, data=v.cpu().numpy())
    print(len(weights7b))
print("Weights for vicuna 7B are saved")
