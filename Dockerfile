FROM ubuntu:22.04

ENV DEBIAN_FRONTEND=noninteractive

# --- System deps (Python + native libs for some Python wheels) ---
RUN apt-get update -y && \
    apt-get install -y --no-install-recommends \
      ca-certificates \
      curl \
      git \
      build-essential \
      pkg-config \
      python3 \
      python3-venv \
      python3-pip \
      libhdf5-dev \
      libopencv-dev \
      libgmp-dev \
      libboost-all-dev \
    && rm -rf /var/lib/apt/lists/*

RUN python3 -m pip install --no-cache-dir --upgrade pip

# --- Poetry (project uses Poetry for deps) ---
RUN python3 -m pip install --no-cache-dir poetry

WORKDIR /app

# Copy everything (simple + robust; slower rebuilds but fewer surprises)
COPY . /app

# Install Python deps into /app/.venv (poetry.toml sets in-project=true)
RUN poetry install --no-interaction --no-ansi

# Make the Poetry venv the default Python
ENV PATH="/app/.venv/bin:${PATH}"
ENV PYTHONPATH="/app"

# --- Install Racket + Rosette (needed for VerificationMethod.ROSETTE) ---
# Note: Installer is interactive; we feed "yes" and the default install location choice.
RUN curl -sSL https://mirror.racket-lang.org/installers/8.7/racket-8.7-x86_64-linux.sh -o /tmp/racket-install.sh && \
    chmod +x /tmp/racket-install.sh && \
    printf "yes\n1\n" | /tmp/racket-install.sh --unix-style --dest /usr/ && \
    rm -f /tmp/racket-install.sh

ENV PATH="${PATH}:/usr/racket/bin"

# Pin Rosette to the same commit used in CI (more stable than "latest")
RUN raco pkg install --auto --skip-installed \
    https://github.com/emina/rosette.git#10178550a0a21e6d80598d0f43c33c9228728f14

# --- Build Bitwuzla (Rosette uses it as the SMT backend) ---
RUN python3 -m pip install --no-cache-dir meson ninja && \
    git clone --depth 1 https://github.com/bitwuzla/bitwuzla /opt/bitwuzla && \
    cd /opt/bitwuzla && \
    ./configure.py && \
    cd /opt/bitwuzla/build && \
    meson compile

# llm/synthesis.py requires this env var for Rosette verification.
ENV BITWUZLA_PATH="/opt/bitwuzla/build/src/main/bitwuzla"

WORKDIR /app

# No default benchmark command.
# Pass the driver at runtime, e.g.:
#   docker run ... llmlift-softmax-part1 python tenspiler/llama/llm/driver/softmax_part1_driver.py
FROM ubuntu:20.04
# Install dependencies
RUN apt-get update -y && \
    apt-get install -y \
    software-properties-common && \
    add-apt-repository ppa:deadsnakes/ppa && \
    apt-get update -y && \
    apt-get install -y \
    python3.9 \
    python3.9-distutils \
    python3.9-venv \
    python3-pip \
    libhdf5-dev \
    g++ \
    git \
    libopencv-dev \
    curl \
    build-essential \
    && rm -rf /var/lib/apt/lists/*
# Set python3.9 as the default python version
RUN update-alternatives --install /usr/bin/python3 python3 /usr/bin/python3.9 1
RUN update-alternatives --install /usr/bin/python python /usr/bin/python3.9 1
# Install pip for Python 3.9
RUN python3.9 -m pip install --upgrade pip
# Install poetry
RUN python3.9 -m pip install poetry
# Set the working directory
WORKDIR /code/tenspiler
COPY pyproject.toml .
RUN poetry lock
RUN poetry install
# Install bitwuzla
WORKDIR /
# Clone Bitwuzla repository
RUN git clone https://github.com/bitwuzla/bitwuzla
WORKDIR /bitwuzla
# Install meson
RUN python3.9 -m pip install meson ninja
RUN ./configure.py
WORKDIR /bitwuzla/build
RUN meson compile


# Install Racket
RUN curl -sSL https://mirror.racket-lang.org/installers/8.7/racket-8.7-x86_64-linux.sh -o racket-install.sh \
    && chmod +x racket-install.sh \
    && echo "yes\n1\n" | ./racket-install.sh --unix-style --dest /usr/ \
    && rm racket-install.sh

# Environment variables to ensure Racket commands are available
ENV PATH="${PATH}:/usr/racket/bin"

# Install Rosette
RUN raco pkg install --auto rosette
#Set back working directory
WORKDIR /code/tenspiler
ENV PYTHONPATH "${PYTHONPATH}:/code/tenspiler"

# move cvc5 binary into docker
COPY ./cvc5 /code/tenspiler/cvc5
ENV PATH="${PATH}:/code/tenspiler/cvc5"
