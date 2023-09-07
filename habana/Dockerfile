FROM ubuntu:20.04

ENV DEBIAN_FRONTEND noninteractive

RUN apt-get update && \
    apt-get -y upgrade && \
    apt-get install -y --no-install-recommends \
        wget \
        ca-certificates \
        cmake \
        gcc \
        g++ \
        libboost-dev \
        git \
        make &&\
    apt-get clean && \
    rm -rf /var/lib/apt/lists/*

RUN wget https://vault.habana.ai/artifactory/debian/focal/pool/main/h/habanatools/habanatools_1.11.0-587_amd64.deb --ca-directory=/etc/ssl/certs/
RUN dpkg -i ./habanatools_1.11.0-587_amd64.deb

# Clone Habana tools
RUN mkdir -p /code
WORKDIR /code
RUN git clone https://github.com/HabanaAI/Habana_Custom_Kernel.git
# Build Habana tools
RUN cd Habana_Custom_Kernel && mkdir build && cd build && cmake .. && make
la