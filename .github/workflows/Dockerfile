ARG K_COMMIT
FROM ghcr.io/foundry-rs/foundry:nightly-56dc7463ce2806c7b410bc605ff7f2916cdbe32a as FOUNDRY

ARG K_COMMIT
FROM runtimeverification:z3 as Z3

ARG K_COMMIT
FROM runtimeverificationinc/kframework-k:ubuntu-focal-${K_COMMIT}

COPY --from=FOUNDRY /usr/local/bin/forge /usr/local/bin/forge
COPY --from=FOUNDRY /usr/local/bin/anvil /usr/local/bin/anvil
COPY --from=FOUNDRY /usr/local/bin/cast /usr/local/bin/cast

RUN    apt-get update                                   \
    && apt-get install --yes software-properties-common \
    && add-apt-repository ppa:ethereum/ethereum

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
            llvm-12              \
            llvm-12-dev          \
            llvm-12-tools        \
            maven                \
            solc                 \
            netcat-openbsd       \
            pkg-config           \
            protobuf-compiler    \
            python3              \
            python3-pip          \
            python-pygments      \
            rapidjson-dev        \
            z3                   \
            zlib1g-dev

COPY --from=Z3 /usr/bin/z3 /usr/bin/z3

RUN pip3 install virtualenv

RUN curl -sL https://deb.nodesource.com/setup_16.x | bash -
RUN    apt-get update               \
    && apt-get upgrade --yes        \
    && apt-get install --yes nodejs

RUN curl -sSL https://get.haskellstack.org/ | sh

RUN curl -sSL https://install.python-poetry.org | POETRY_HOME=/usr python3 - && poetry --version

ARG USER_ID=1000
ARG GROUP_ID=1000
RUN groupadd -g $GROUP_ID user && useradd -m -u $USER_ID -s /bin/sh -g user user

USER user:user
WORKDIR /home/user

RUN    git config --global user.email 'admin@runtimeverification.com' \
    && git config --global user.name  'RV Jenkins'                    \
    && mkdir -p ~/.ssh                                                \
    && echo 'host github.com'                       > ~/.ssh/config   \
    && echo '    hostname github.com'              >> ~/.ssh/config   \
    && echo '    user git'                         >> ~/.ssh/config   \
    && echo '    identityagent SSH_AUTH_SOCK'      >> ~/.ssh/config   \
    && echo '    stricthostkeychecking accept-new' >> ~/.ssh/config   \
    && chmod go-rwx -R ~/.ssh
