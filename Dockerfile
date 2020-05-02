ARG K_COMMIT
FROM runtimeverificationinc/kframework-k:ubuntu-bionic-${K_COMMIT}

RUN    apt-get update                \
    && apt-get upgrade --yes         \
    && apt-get install --yes         \
            libboost-test-dev        \
            libcrypto++-dev          \
            libgflags-dev            \
            libprocps-dev            \
            libsecp256k1-dev         \
            libssl-dev               \
            netcat-openbsd           \
            pandoc                   \
            pkg-config               \
            python3                  \
            python-pygments          \
            python-recommonmark      \
            python-sphinx            \
            rapidjson-dev

RUN curl -sL https://deb.nodesource.com/setup_10.x | bash -
RUN apt-get install --yes nodejs

USER user:user

ENV LD_LIBRARY_PATH=/usr/local/lib
ENV PATH=/home/user/.local/bin:$PATH
