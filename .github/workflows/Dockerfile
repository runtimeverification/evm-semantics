ARG K_COMMIT
ARG Z3_VERSION
FROM ghcr.io/foundry-rs/foundry:nightly-aeba75e4799f1e11e3daba98d967b83e286b0c4a as FOUNDRY

ARG K_COMMIT
ARG Z3_VERSION
FROM z3:${Z3_VERSION} as Z3

ARG K_COMMIT
FROM runtimeverificationinc/kframework-k:ubuntu-jammy-${K_COMMIT}

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

RUN curl -sSL https://install.python-poetry.org | POETRY_HOME=/usr python3 - --version 1.3.2

ARG USER_ID=1000
ARG GROUP_ID=1000
RUN groupadd -g $GROUP_ID user && useradd -m -u $USER_ID -s /bin/sh -g user user

USER user:user
WORKDIR /home/user
