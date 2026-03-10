import os
from pathlib import Path

from dotenv import load_dotenv

load_dotenv()

BEDROCK_MODEL_ID = os.getenv(
    "BEDROCK_MODEL_ID", "us.anthropic.claude-sonnet-4-20250514-v1:0"
)

INDENTATION = " " * 4
TEMPLATE_SYS = "You are a helpful expert in programming languages."
TEMPLATE_ERR = "These generated programs are incorrect. Do not generate the same. Please generate another program."
TEMPLATE_ENCLOSE_CODE = "Please enclose your solution in a python code block"
SYNTHESIS_LOGS_DIR = Path("./synthesisLogs")
