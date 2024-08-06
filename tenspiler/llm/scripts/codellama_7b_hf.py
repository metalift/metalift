import os

import requests

hf_token = os.getenv("HUGGING_FACE_API")
if not hf_token:
    raise ValueError("Please set the environment variable HUGGING_FACE_API")

API_URL = "https://api-inference.huggingface.co/models/codellama/CodeLlama-7b-hf"
headers = {"Authorization": f"Bearer {hf_token}"}


def query(payload):
    response = requests.post(API_URL, headers=headers, json=payload)
    return response.json()


output = query(
    {
        "inputs": "Write a python program to split a string into characters ",
    }
)

print(output[0]["generated_text"])
