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
    libopencv-dev && \
    rm -rf /var/lib/apt/lists/*
# Set python3.9 as the default python version
RUN update-alternatives --install /usr/bin/python3 python3 /usr/bin/python3.9 1
RUN update-alternatives --install /usr/bin/python python /usr/bin/python3.9 1
# Install pip for Python 3.9
RUN python3.9 -m pip install --upgrade pip
# Install poetry
RUN python3.9 -m pip install poetry
# Set the working directory
WORKDIR /code/metalift
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