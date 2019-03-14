FROM ubuntu:bionic

ENV TZ=America/Chicago
RUN    ln --symbolic --no-dereference --force /usr/share/zoneinfo/$TZ /etc/localtime \
    && echo $TZ > /etc/timezone

RUN    apt update                                                                  \
    && apt upgrade --yes                                                           \
    && apt install --yes                                                           \
           autoconf curl flex gcc libffi-dev libmpfr-dev libtool llvm-6.0-tools    \
           make maven opam openjdk-8-jdk pandoc pkg-config python3 python-pygments \
           python-recommonmark python-sphinx time zlib1g-dev libcrypto++-dev       \
           libsecp256k1-dev cmake libssl-dev libprocps-dev clang-6.0 bison         \
           libboost-test-dev libyaml-cpp-dev libjemalloc-dev

RUN update-alternatives --set java /usr/lib/jvm/java-8-openjdk-amd64/jre/bin/java

RUN curl -sSL https://get.haskellstack.org/ | sh

RUN    git clone 'https://github.com/z3prover/z3' --branch=z3-4.6.0 \
    && cd z3                                                        \
    && python scripts/mk_make.py                                    \
    && cd build                                                     \
    && make -j8                                                     \
    && make install                                                 \
    && cd ../..                                                     \
    && rm -rf z3

RUN    git clone 'https://github.com/scipr-lab/libff' --recursive        \
    && cd libff                                                         \
    && mkdir build                                                      \
    && cd build                                                         \
    && CC=clang-6.0 CXX=clang++-6.0 cmake .. -DCMAKE_BUILD_TYPE=Release \
    && make -j8                                                         \
    && make install                                                     \
    && cd ../..                                                         \
    && rm -rf libff

ARG USER_ID=1000
ARG GROUP_ID=1000
RUN    groupadd --gid $GROUP_ID user                                        \
    && useradd --create-home --uid $USER_ID --shell /bin/sh --gid user user

USER $USER_ID:$GROUP_ID

ADD --chown=user:user .build/k/llvm-backend/src/main/native/llvm-backend/install-rust .build/k/llvm-backend/src/main/native/llvm-backend/rust-checksum /home/user/.install-rust/
RUN    cd /home/user/.install-rust \
    && ./install-rust

ADD .build/k/k-distribution/src/main/scripts/bin/k-configure-opam-dev .build/k/k-distribution/src/main/scripts/bin/k-configure-opam-common /home/user/.tmp-opam/bin/
ADD .build/k/k-distribution/src/main/scripts/lib/opam  /home/user/.tmp-opam/lib/opam/
RUN    cd /home/user \
    && ./.tmp-opam/bin/k-configure-opam-dev

ENV LC_ALL=C.UTF-8
ADD --chown=user:user .build/k/haskell-backend/src/main/native/haskell-backend/stack.yaml /home/user/.tmp-haskell/
ADD --chown=user:user .build/k/haskell-backend/src/main/native/haskell-backend/kore/package.yaml /home/user/.tmp-haskell/kore/
RUN    cd /home/user/.tmp-haskell \
    && stack build --only-snapshot --test --bench --no-haddock-deps --haddock --library-profiling

ENV LD_LIBRARY_PATH=/usr/local/lib
