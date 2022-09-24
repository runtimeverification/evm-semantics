ARG K_COMMIT
ARG Z3_VERSION

FROM ghcr.io/foundry-rs/foundry:nightly-56dc7463ce2806c7b410bc605ff7f2916cdbe32a as FOUNDRY
FROM z3:${Z3_VERSION} as Z3
FROM runtimeverificationinc/kframework-k:ubuntu-focal-${K_COMMIT}

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
            protobuf-compiler \
            python3           \
            python3-pip       \
            solc

RUN pip3 install virtualenv
RUN curl -sSL https://install.python-poetry.org | POETRY_HOME=/usr python3 - && poetry --version

ARG USER_ID=1000
ARG GROUP_ID=1000
RUN groupadd -g $GROUP_ID user && useradd -m -u $USER_ID -s /bin/sh -g user user

USER user:user
WORKDIR /home/user
