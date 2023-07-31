ARG K_COMMIT
ARG Z3_VERSION
FROM ghcr.io/foundry-rs/foundry:nightly-d93312bfe5d419d63a9836fce31f9f60a4523519 as FOUNDRY

ARG K_COMMIT
ARG Z3_VERSION
FROM z3:${Z3_VERSION} as Z3

ARG K_COMMIT
FROM runtimeverificationinc/kframework-k:ubuntu-jammy-${K_COMMIT}

COPY --from=FOUNDRY /usr/local/bin/forge /usr/local/bin/forge
COPY --from=FOUNDRY /usr/local/bin/anvil /usr/local/bin/anvil
COPY --from=FOUNDRY /usr/local/bin/cast /usr/local/bin/cast

COPY --from=Z3 /usr/bin/z3 /usr/bin/z3

ARG LLVM_VERSION

RUN    apt-get update                  \
    && apt-get upgrade --yes           \
    && apt-get install --yes           \
            cargo                      \
            clang-${LLVM_VERSION}      \
            cmake                      \
            curl                       \
            debhelper                  \
            libboost-test-dev          \
            libprocps-dev              \
            libssl-dev                 \
            llvm-${LLVM_VERSION}-dev   \
            llvm-${LLVM_VERSION}-tools \
            netcat                     \
            protobuf-compiler          \
            python3                    \
            python3-pip

ARG USER_ID=1000
ARG GROUP_ID=1000
RUN groupadd -g $GROUP_ID user && useradd -m -u $USER_ID -s /bin/sh -g user user

USER user:user
RUN mkdir /home/user/workspace
WORKDIR /home/user/workspace

ENV PATH=/home/user/.cargo/bin:/home/user/.local/bin:${PATH}

RUN    curl -sSL https://install.python-poetry.org | python3 - \
    && poetry --version

RUN    cargo install svm-rs --version 0.3.0 \
    && svm install 0.8.13                   \
    && solc --version
