ARG LLVM_VERSION
ARG K_COMMIT
ARG K_VERSION
ARG Z3_VERSION
ARG BASE_DISTRO
FROM ghcr.io/foundry-rs/foundry:nightly-ca67d15f4abd46394b324c50e21e66f306a1162d as FOUNDRY

ARG LLVM_VERSION
ARG K_COMMIT
ARG K_VERSION
ARG Z3_VERSION
ARG BASE_DISTRO
FROM z3:${Z3_VERSION} as Z3

ARG LLVM_VERSION
ARG K_VERSION
ARG BASE_DISTRO
FROM stack:${BASE_DISTRO}-${K_VERSION} as STACK

ARG LLVM_VERSION
ARG K_COMMIT
FROM runtimeverificationinc/kframework-k:ubuntu-jammy-${K_COMMIT}

COPY --from=FOUNDRY /usr/local/bin/forge /usr/local/bin/forge
COPY --from=FOUNDRY /usr/local/bin/anvil /usr/local/bin/anvil
COPY --from=FOUNDRY /usr/local/bin/cast /usr/local/bin/cast

COPY --from=Z3 /usr/bin/z3 /usr/bin/z3

COPY --from=STACK /usr/local/bin/stack /usr/local/bin/stack

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
            libcrypto++-dev            \
            libprocps-dev              \
            libssl-dev                 \
            libyaml-dev                \
            llvm-${LLVM_VERSION}-dev   \
            llvm-${LLVM_VERSION}-tools \
            maven                      \
            netcat                     \
            protobuf-compiler          \
            maven                      \
            python3                    \
            python3-pip

ARG USER
ARG GROUP
ARG USER_ID
ARG GROUP_ID
RUN groupadd -g ${GROUP_ID} ${GROUP} && useradd -m -u ${USER_ID} -s /bin/sh -g ${GROUP} ${USER}

USER ${USER}:${GROUP}
RUN mkdir /home/${USER}/workspace
WORKDIR /home/${USER}/workspace

ENV PATH=/home/${USER}/.cargo/bin:/home/${USER}/.local/bin:/usr/local/bin/:${PATH}

RUN    curl -sSL https://install.python-poetry.org | python3 - \
    && poetry --version

RUN    cargo install svm-rs --version 0.3.0 \
    && svm install 0.8.13                   \
    && solc --version

COPY --from=STACK --chown=$USER:$GROUP /home/$USER/.stack /home/$USER/.stack
