ARG K_COMMIT
FROM runtimeverificationinc/kframework-k:ubuntu-focal-${K_COMMIT}

RUN    apt-get update            \
    && apt-get upgrade --yes     \
    && apt-get install --yes     \
            cmake                \
            curl                 \
            debhelper            \
            default-jdk-headless \
            jq                   \
            libboost-test-dev    \
            libcrypto++-dev      \
            libgflags-dev        \
            libprocps-dev        \
            libsecp256k1-dev     \
            libssl-dev           \
            libyaml-dev          \
            maven                \
            netcat-openbsd       \
            pkg-config           \
            protobuf-compiler    \
            python3              \
            python-pygments      \
            rapidjson-dev        \
            z3                   \
            zlib1g-dev

RUN    git clone 'https://github.com/z3prover/z3' --branch=z3-4.8.11 \
    && cd z3                                                         \
    && python scripts/mk_make.py                                     \
    && cd build                                                      \
    && make -j8                                                      \
    && make install                                                  \
    && cd ../..                                                      \
    && rm -rf z3

RUN curl -sL https://deb.nodesource.com/setup_14.x | bash -
RUN    apt-get update               \
    && apt-get upgrade --yes        \
    && apt-get install --yes nodejs

RUN curl -sSL https://get.haskellstack.org/ | sh

ARG USER_ID=1000
ARG GROUP_ID=1000
RUN groupadd -g $GROUP_ID user && useradd -m -u $USER_ID -s /bin/sh -g user user

USER user:user
WORKDIR /home/user

RUN curl -L https://github.com/github/hub/releases/download/v2.14.0/hub-linux-amd64-2.14.0.tgz -o /home/user/hub.tgz
RUN cd /home/user && tar xzf hub.tgz

ENV PATH=/home/user/hub-linux-amd64-2.14.0/bin:$PATH

RUN    git config --global user.email 'admin@runtimeverification.com' \
    && git config --global user.name  'RV Jenkins'                    \
    && mkdir -p ~/.ssh                                                \
    && echo 'host github.com'                       > ~/.ssh/config   \
    && echo '    hostname github.com'              >> ~/.ssh/config   \
    && echo '    user git'                         >> ~/.ssh/config   \
    && echo '    identityagent SSH_AUTH_SOCK'      >> ~/.ssh/config   \
    && echo '    stricthostkeychecking accept-new' >> ~/.ssh/config   \
    && chmod go-rwx -R ~/.ssh
