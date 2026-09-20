FROM ubuntu:24.04

ARG DEBIAN_FRONTEND=noninteractive

RUN apt-get update \
    && apt-get install -y --no-install-recommends \
        ca-certificates \
        dotnet-runtime-8.0 \
        tar \
    && rm -rf /var/lib/apt/lists/*

RUN mkdir -p /opt/coreutils-fuzzer-staging /fuzz/work /fuzz/shared \
    && chmod 0755 /opt/coreutils-fuzzer-staging /fuzz /fuzz/work /fuzz/shared

WORKDIR /fuzz

CMD ["sleep", "infinity"]
