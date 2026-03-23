# LLMLift
LLMLift is an LLM-based approach for building verified-lifting tools. LLMLift builds over [MetaLift](https://metalift.pages.dev/) by replacing its symbolic synthesis engine with an LLM.

Check out the full paper [here](https://openreview.net/forum?id=spwE9sLrfg), accepted at NeurIPS 2024.

## Getting started

### Installation

#### Get source code
First, clone the MetaLift repository with branch `asplos`.
```bash
git clone --branch asplos https://github.com/metalift/metalift.git
```

#### Build docker image
```bash
docker build -f Dockerfile.tutorial -t llmlift-tutorial .
```


#### Running Benchmarks
We support Claude, Gemini, GPT, and AWS Bedrock (which hosts Claude and other models) for synthesis. For Claude, Gemini, or GPT, set the corresponding API keys (`OPENAI_API_KEY`, `CLAUDE_API_KEY`, `GEMINI_API_KEY`) in a `.env` file.

The tutorial uses **Bedrock**. Authenticate by mounting your `~/.aws` folder into the container so boto3 can read credentials from `~/.aws/credentials` and `~/.aws/config`. You can start an interactive shell by running the following:

```bash
docker run --rm -it -v ~/.aws:/root/.aws:ro llmlift-tutorial bash
```

Inside the interactive shell, you can run benchmarks such as `python tests/tutorial/rmsnorm/rmsnorm_driver.py`.
You can override the Bedrock model or region via `BEDROCK_MODEL_ID` and `AWS_REGION` environment variables.
