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

RUN    git config --global user.email 'admin@runtimeverification.com' \
    && git config --global user.name  'RV Jenkins'                    \
    && mkdir -p ~/.ssh                                                \
    && echo 'host github.com'                       > ~/.ssh/config   \
    && echo '    hostname github.com'              >> ~/.ssh/config   \
    && echo '    user git'                         >> ~/.ssh/config   \
    && echo '    identityagent SSH_AUTH_SOCK'      >> ~/.ssh/config   \
    && echo '    stricthostkeychecking accept-new' >> ~/.ssh/config   \
    && chmod go-rwx -R ~/.ssh
