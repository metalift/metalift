import os
from pathlib import Path

import anthropic
import boto3
from dotenv import load_dotenv
from openai import OpenAI

load_dotenv()
OPENAI_CLIENT = OpenAI(api_key=os.getenv("OPENAI_API_KEY"))
CLAUDE_CLIENT = anthropic.Anthropic(api_key=os.getenv("CLAUDE_API_KEY"))
BEDROCK_CLIENT = boto3.client(
    "bedrock-runtime",
    region_name=os.getenv("AWS_REGION", "us-east-1"),
)
BEDROCK_MODEL_ID = os.getenv(
    "BEDROCK_MODEL_ID", "us.anthropic.claude-sonnet-4-20250514-v1:0"
)

INDENTATION = " " * 4
TEMPLATE_SYS = "You are a helpful expert in programming languages."
TEMPLATE_ERR = "These generated programs are incorrect. Do not generate the same. Please generate another program."
TEMPLATE_ENCLOSE_CODE = "Please enclose your solution in a python code block"
SYNTHESIS_LOGS_DIR = Path("./synthesisLogs")
