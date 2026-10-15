FROM mcr.microsoft.com/devcontainers/base:ubuntu-24.04

ARG DEBIAN_FRONTEND=noninteractive
ARG Z3_VERSION=4.16.0
ARG Z3_RELEASE=snapshot-2026-04-03

SHELL ["/bin/bash", "-o", "pipefail", "-c"]

ENV TZ=Etc/UTC \
    LANG=C.UTF-8 \
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

RUN mkdir -p /opt/z3/bin \
    && curl -fsSL "https://github.com/dafny-lang/solver-builds/releases/download/${Z3_RELEASE}/z3-${Z3_VERSION}-x64-ubuntu-24.04-bin.zip" -o /tmp/z3.zip \
    && unzip /tmp/z3.zip -d /opt/z3/bin \
    && rm /tmp/z3.zip \
    && chmod +x "/opt/z3/bin/z3-${Z3_VERSION}" \
    && ln -s "/opt/z3/bin/z3-${Z3_VERSION}" /usr/local/bin/z3 \
    && z3 --version | grep -F "Z3 version ${Z3_VERSION} "

RUN ln -snf "/usr/share/zoneinfo/${TZ}" /etc/localtime \
    && echo "${TZ}" > /etc/timezone

RUN wget -q https://packages.microsoft.com/config/ubuntu/24.04/packages-microsoft-prod.deb -O /tmp/packages-microsoft-prod.deb \
    && dpkg -i /tmp/packages-microsoft-prod.deb \
    && rm -f /tmp/packages-microsoft-prod.deb \
    && apt-get update \
    && apt-get install -y --no-install-recommends dotnet-sdk-8.0 \
    && rm -rf /var/lib/apt/lists/*

RUN ln -s /workspace/dafnyutils/dafny/Binaries/Dafny /usr/bin/dafny-benchmark

ENV PATH="/home/vscode/.cargo/bin:${PATH}"

RUN usermod --shell /usr/bin/zsh vscode \
    && install -d -m 0755 -o vscode -g vscode /workspace/tmp

USER vscode

# The differential checker is built with the Rust toolchain.
RUN curl -fsSL https://sh.rustup.rs | sh -s -- -y --profile minimal --default-toolchain stable \
    && /home/vscode/.cargo/bin/rustup component add clippy rustfmt
