ARG BASE_OS
ARG BASE_DISTRO
ARG K_VERSION
ARG Z3_VERSION
FROM ghcr.io/foundry-rs/foundry:nightly-56dc7463ce2806c7b410bc605ff7f2916cdbe32a as FOUNDRY

ARG BASE_OS
ARG BASE_DISTRO
ARG K_VERSION
ARG Z3_VERSION
FROM z3:${BASE_DISTRO}-${Z3_VERSION} as Z3

ARG K_VERSION
FROM runtimeverificationinc/kframework-k:${BASE_OS}-${BASE_DISTRO}-${K_VERSION}

COPY --from=FOUNDRY /usr/local/bin/forge /usr/local/bin/forge
COPY --from=FOUNDRY /usr/local/bin/anvil /usr/local/bin/anvil
COPY --from=FOUNDRY /usr/local/bin/cast /usr/local/bin/cast

COPY --from=Z3 /usr/bin/z3 /usr/bin/z3

RUN    apt-get update                                   \
    && apt-get install --yes software-properties-common \
    && add-apt-repository ppa:ethereum/ethereum

RUN    apt-get update         \
    && apt-get upgrade --yes  \
    && apt-get install --yes  \
            cmake             \
            curl              \
            libcrypto++-dev   \
            libprocps-dev     \
            libsecp256k1-dev  \
            libssl-dev        \
            netcat            \
            protobuf-compiler \
            python3           \
            python3-pip       \
            solc

RUN pip3 install virtualenv
RUN curl -sSL https://install.python-poetry.org | POETRY_HOME=/usr python3 - --version 1.2.2

# The image is built specifically for an environment with this user/group
ARG USER=github-user
ARG GROUP=$USER
ARG USER_ID=1000
ARG GROUP_ID=$USER_ID
RUN groupadd -g $GROUP_ID $GROUP && useradd -m -u $USER_ID -s /bin/sh -g $GROUP $USER

USER $USER:$GROUP
