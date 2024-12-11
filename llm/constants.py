import os
from pathlib import Path

import anthropic
from dotenv import load_dotenv
from openai import OpenAI

load_dotenv()
OPENAI_CLIENT = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))
CLAUDE_CLIENT = anthropic.Anthropic(api_key=os.getenv("CLAUDE_API_KEY"))

INDENTATION = " " * 4
TEMPLATE_SYS = "You are a helpful expert in programming languages."
TEMPLATE_ERR = "These generated programs are incorrect. Do not generate the same. Please generate another program."
TEMPLATE_ENCLOSE_CODE = "Please enclose your solution in a python code block"
SYNTHESIS_LOGS_DIR = Path("./synthesisLogs")
