FROM mcr.microsoft.com/devcontainers/base:ubuntu-24.04

ARG DEBIAN_FRONTEND=noninteractive

SHELL ["/bin/bash", "-o", "pipefail", "-c"]

ENV LANG=C.UTF-8 \
    LANGUAGE=C.UTF-8 \
    LC_ALL=C.UTF-8 \
    DOTNET_ROOT=/usr/share/dotnet \
    DOTNET_CLI_TELEMETRY_OPTOUT=1 \
    DOTNET_NOLOGO=1

RUN apt-get update \
    && apt-get install -y --no-install-recommends \
        autoconf \
        automake \
        autopoint \
        bison \
        build-essential \
        bubblewrap \
        ca-certificates \
        curl \
        file \
        flex \
        gawk \
        gettext \
        git \
        gnupg \
        gperf \
        gzip \
        help2man \
        jq \
        libtool \
        m4 \
        make \
        openssh-client \
        patch \
        perl \
        pkg-config \
        python3 \
        python3-pip \
        python3-venv \
        ripgrep \
        rsync \
        tar \
        texinfo \
        util-linux \
        unzip \
        wget \
        xz-utils \
        z3 \
    && rm -rf /var/lib/apt/lists/*

RUN wget -q https://packages.microsoft.com/config/ubuntu/24.04/packages-microsoft-prod.deb -O /tmp/packages-microsoft-prod.deb \
    && dpkg -i /tmp/packages-microsoft-prod.deb \
    && rm -f /tmp/packages-microsoft-prod.deb \
    && apt-get update \
    && apt-get install -y --no-install-recommends \
        dotnet-sdk-8.0 \
    && rm -rf /var/lib/apt/lists/*

COPY requirements.txt /tmp/evaluation-requirements.txt

RUN python3 -m venv /opt/pytools \
    && /opt/pytools/bin/pip install --no-cache-dir --upgrade pip setuptools wheel \
    && /opt/pytools/bin/pip install --no-cache-dir -r /tmp/evaluation-requirements.txt \
    && rm -f /tmp/evaluation-requirements.txt

COPY pyproject.toml /tmp/dafnyutils-package/pyproject.toml
COPY src/ /tmp/dafnyutils-package/src/
RUN /opt/pytools/bin/pip install --no-cache-dir --no-deps /tmp/dafnyutils-package \
    && rm -rf /tmp/dafnyutils-package

RUN mkdir -p /tmp/nuget-prewarm \
    && cd /tmp/nuget-prewarm \
    && NUGET_PACKAGES=/opt/eval-cache/nuget/packages dotnet new console --force >/dev/null \
    && for package in System.Runtime.Numerics::4.3.0 System.Collections.Immutable::1.7.1; do \
        NUGET_PACKAGES=/opt/eval-cache/nuget/packages dotnet add package "${package%%::*}" \
            --version "${package##*::}" >/dev/null; \
    done \
    && rm -rf /tmp/nuget-prewarm

ENV PATH="/run/tools:/opt/pytools/bin:/opt/eval-cache/cargo/bin:${PATH}" \
    PYTHONDONTWRITEBYTECODE=1 \
    PYTHONPYCACHEPREFIX=/run/pycache

COPY Binaries/ /opt/dafnyutils-dafny/Binaries/
RUN ln -s /opt/dafnyutils-dafny/Binaries/Dafny /usr/bin/dafny-benchmark

RUN install -d -m 0755 -o root -g root /workspace
WORKDIR /workspace
