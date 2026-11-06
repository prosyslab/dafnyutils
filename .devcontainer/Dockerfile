FROM mcr.microsoft.com/devcontainers/base:ubuntu-24.04 AS base

ARG DEBIAN_FRONTEND=noninteractive

SHELL ["/bin/bash", "-o", "pipefail", "-c"]

ENV TZ=Etc/UTC \
    LANG=C.UTF-8 \
    LANGUAGE=C.UTF-8 \
    LC_ALL=C.UTF-8

RUN apt-get update \
    && apt-get install -y --no-install-recommends \
        autoconf \
        automake \
        autopoint \
        bash-completion \
        bison \
        build-essential \
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
        less \
        libicu74 \
        libtool \
        locales \
        m4 \
        make \
        openssh-client \
        openjdk-17-jdk \
        patch \
        perl \
        pkg-config \
        python3 \
        python-is-python3 \
        python3-pip \
        python3-pytest \
        python3-pytest-xdist \
        python3-venv \
        ripgrep \
        rsync \
        tar \
        texinfo \
        tmux \
        tzdata \
        util-linux \
        unzip \
        wget \
        xz-utils \
        zsh \
    && rm -rf /var/lib/apt/lists/*

RUN ln -snf "/usr/share/zoneinfo/${TZ}" /etc/localtime \
    && echo "${TZ}" > /etc/timezone

# Pinned .NET SDK for Dafny and the C# benchmark executables. Microsoft's versioned
# tarball stays downloadable, unlike a superseded Ubuntu package version.
ARG DOTNET_SDK_VERSION=8.0.133
ARG DOTNET_SDK_SHA512=5a2a34c388f17ffb3c1adfec113428c70152749c23c0307ab65d2f17eeb56125f0f4a2ff2bb66c9b045a1d4241ea27926e223d6990b6cd7ea29b3cede20b6a7c
ENV DOTNET_ROOT=/usr/share/dotnet \
    DOTNET_CLI_TELEMETRY_OPTOUT=1 \
    DOTNET_NOLOGO=1

RUN if [ "$(dpkg --print-architecture)" != amd64 ]; then \
        echo "The pinned .NET SDK checksum and Z3 snapshot support x86_64 only." >&2; exit 1; \
    fi \
    && curl -fsSL -o /tmp/dotnet-sdk.tar.gz \
        "https://builds.dotnet.microsoft.com/dotnet/Sdk/${DOTNET_SDK_VERSION}/dotnet-sdk-${DOTNET_SDK_VERSION}-linux-x64.tar.gz" \
    && echo "${DOTNET_SDK_SHA512}  /tmp/dotnet-sdk.tar.gz" | sha512sum --check --strict - \
    && mkdir -p "${DOTNET_ROOT}" \
    && tar -xzf /tmp/dotnet-sdk.tar.gz -C "${DOTNET_ROOT}" \
    && rm /tmp/dotnet-sdk.tar.gz \
    && ln -s "${DOTNET_ROOT}/dotnet" /usr/local/bin/dotnet \
    && test "$(dotnet --version)" = "${DOTNET_SDK_VERSION}"

FROM base AS dafny-build

# dafny-version.toml is the only place that records the Dafny fork URL and commit.
COPY dafny-version.toml /tmp/dafny-version.toml
RUN read_pin() { \
        python3 -c 'import sys, tomllib; print(tomllib.load(open(sys.argv[1], "rb"))[sys.argv[2]])' \
            /tmp/dafny-version.toml "$1"; \
    } \
    && repo="$(read_pin repo)" \
    && commit="$(read_pin commit)" \
    && [[ "${commit}" =~ ^[0-9a-f]{40}$ ]] \
    && git init --quiet /tmp/dafny \
    && git -C /tmp/dafny fetch --depth 1 "${repo}" "${commit}" \
    && git -C /tmp/dafny checkout --detach FETCH_HEAD \
    && mkdir /tmp/z3-download \
    && cd /tmp/z3-download \
    && make -f /tmp/dafny/Makefile z3-ubuntu \
    && dotnet build /tmp/dafny/Source/Dafny.sln --no-incremental -m:1 -nodeReuse:false \
        -p:UseSharedCompilation=false -p:PathMap=/tmp/dafny=/src/dafny \
        -p:ContinuousIntegrationBuild=true -p:Deterministic=true \
    && [[ "$(/tmp/dafny/Binaries/Dafny --version)" == *"+${commit}" ]] \
    && test -x /tmp/dafny/Binaries/z3/bin/z3-4.16.0 \
    && test -x /tmp/dafny/Binaries/z3/bin/z3-4.12.1

FROM base

COPY --from=dafny-build /tmp/dafny/Binaries /opt/dafny
RUN ln -s /opt/dafny/Dafny /usr/local/bin/dafny

ENV PATH="/home/vscode/.cargo/bin:${PATH}"

RUN usermod --shell /usr/bin/zsh vscode \
    && install -d -m 0755 -o vscode -g vscode /workspace/tmp

USER vscode

# The differential checker is built with the Rust toolchain.
RUN curl -fsSL https://sh.rustup.rs | sh -s -- -y --profile minimal --default-toolchain stable \
    && /home/vscode/.cargo/bin/rustup component add clippy rustfmt
