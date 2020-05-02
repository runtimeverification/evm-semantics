ARG K_COMMIT
FROM runtimeverificationinc/kframework-k:ubuntu-bionic-${K_COMMIT}

RUN    sudo apt-get update           \
    && sudo apt-get upgrade --yes    \
    && sudo apt-get install --yes    \
                 cmake               \
                 libboost-test-dev   \
                 libcrypto++-dev     \
                 libgflags-dev       \
                 libprocps-dev       \
                 libsecp256k1-dev    \
                 libssl-dev          \
                 netcat-openbsd      \
                 pandoc              \
                 pkg-config          \
                 python3             \
                 python-pygments     \
                 python-recommonmark \
                 python-sphinx       \
                 rapidjson-dev

RUN curl -sL https://deb.nodesource.com/setup_10.x | bash -
RUN sudo apt-get install --yes nodejs
