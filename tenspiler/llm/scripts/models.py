import copy
import os
from enum import Enum
from typing import Any

import anthropic
import google.generativeai as genai
from dotenv import load_dotenv
from openai import OpenAI

from tenspiler.llm.scripts.utils import TEMPLATE_SYS, extract, replace_ite

load_dotenv()

openai_client = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))
claude_client = anthropic.Anthropic(api_key=os.getenv("CLAUDE_API_KEY"))
gemini_client = genai.configure(api_key=os.getenv("GEMINI_API_KEY"))


class LLMModel(Enum):
    CLAUDE = "claude"
    GPT = "gpt"
    GEMINI = "gemini"


def get_solution_from_claude(messages: list[dict[str, Any]]) -> str:
    print("running with claude")
    message = claude_client.messages.create(
        model="claude-3-5-sonnet-20240620",
        max_tokens=1000,
        temperature=0.7,
        system=TEMPLATE_SYS,
        messages=messages,
    )
    raw_solutions = extract(message.content[0].text)
    return [replace_ite(raw_solution) for raw_solution in raw_solutions]


def get_solution_from_gpt(messages: list[dict[str, Any]]) -> str:
    print("running with gpt")
    messages_with_sys = [{"role": "system", "content": TEMPLATE_SYS}, *messages]
    outputs = openai_client.chat.completions.create(
        model="gpt-4",  # model to use gpt-4o-2024-08-06
        messages=messages_with_sys,
        n=1,
        temperature=0.7,
    )
    outputs = [choice.message.content for choice in outputs.choices]
    raw_output = extract(outputs[0])[0]
    extracted_output = replace_ite(raw_output)
    return extracted_output


def get_solution_from_gemini(messages: list[dict[str, Any]]) -> str:
    print("running with gemini")
    messages_copy = copy.deepcopy(messages)
    for message in messages_copy:
        if message["role"] == "assistant":
            message["role"] = "model"
        message["parts"] = message["content"]
        del message["content"]

    generation_config = {
        "temperature": 0.7,
        "top_p": 0.95,
        "top_k": 64,
        "max_output_tokens": 8192,
        "response_mime_type": "text/plain",
    }

    model = genai.GenerativeModel(
        model_name="gemini-1.5-pro-exp-0827",  # "gemini-1.5-pro-exp-0827",
        generation_config=generation_config,
    )

    chat_session = model.start_chat(history=messages_copy[:-1])
    response = chat_session.send_message(messages_copy[-1]["parts"])
    print("RAW RESPONSE", response.text)
    raw_solution = extract(response.text)[0]
    extracted_solution = replace_ite(raw_solution)
    return extracted_solution


def get_solution_from_llm(llm_model: LLMModel, messages: list[dict[str, Any]]) -> str:
    if llm_model == LLMModel.CLAUDE:
        return get_solution_from_claude(messages)
    elif llm_model == LLMModel.GPT:
        return get_solution_from_gpt(messages)
    elif llm_model == LLMModel.GEMINI:
        return get_solution_from_gemini(messages)
    raise ValueError(f"Invalid LLM model {llm_model}")
