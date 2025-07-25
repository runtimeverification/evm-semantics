ARG Z3_VERSION
ARG K_VERSION
ARG BASE_DISTRO
ARG LLVM_VERSION

ARG Z3_VERSION
FROM runtimeverificationinc/z3:ubuntu-jammy-${Z3_VERSION} as Z3

ARG K_VERSION
FROM runtimeverificationinc/kframework-k:ubuntu-jammy-${K_VERSION}

COPY --from=Z3 /usr/bin/z3 /usr/bin/z3

ARG LLVM_VERSION

RUN    apt-get update                  \
    && apt-get upgrade --yes           \
    && apt-get install --yes           \
            clang-${LLVM_VERSION}      \
            cmake                      \
            curl                       \
            debhelper                  \
            libboost-test-dev          \
            libcrypto++-dev            \
            libsecp256k1-dev           \
            libssl-dev                 \
            libyaml-dev                \
            llvm-${LLVM_VERSION}-dev   \
            llvm-${LLVM_VERSION}-tools \
            maven                      \
            python3                    \
            python3-pip

ARG USER=user
ARG GROUP
ARG USER_ID
ARG GROUP_ID
RUN groupadd -g ${GROUP_ID} ${GROUP} && useradd -m -u ${USER_ID} -s /bin/sh -g ${GROUP} ${USER}

USER ${USER}:${GROUP}
RUN mkdir /home/${USER}/workspace
WORKDIR /home/${USER}/workspace

ENV PATH=/home/${USER}/.local/bin:${PATH}

ARG UV_VERSION
RUN    curl -LsSf https://astral.sh/uv/${UV_VERSION}/install.sh | sh \
    && uv --version
