FROM runtimeverificationinc/ubuntu:bionic

RUN    apt-get update            \
    && apt-get upgrade --yes     \
    && apt-get install --yes     \
        autoconf                 \
        binutils-dev             \
        bison                    \
        clang-8                  \
        cmake                    \
        curl                     \
        flex                     \
        g++                      \
        gcc                      \
        gperf                    \
        libboost-all-dev         \
        libcap-dev               \
        libcrypto++-dev          \
        libdouble-conversion-dev \
        libevent-dev             \
        libffi-dev               \
        libgflags-dev            \
        libgoogle-glog-dev       \
        libiberty-dev            \
        libjemalloc-dev          \
        libkrb5-dev              \
        liblz4-dev               \
        liblzma-dev              \
        libmpfr-dev              \
        libnuma-dev              \
        libprocps-dev            \
        libprotobuf-dev          \
        libsasl2-dev             \
        libsecp256k1-dev         \
        libsnappy-dev            \
        libsodium-dev            \
        libssl-dev               \
        libtool                  \
        libyaml-dev              \
        libzstd-dev              \
        lld-8                    \
        llvm-8-tools             \
        make                     \
        maven                    \
        netcat-openbsd           \
        opam                     \
        openjdk-11-jdk           \
        pandoc                   \
        pkg-config               \
        protobuf-compiler        \
        python3                  \
        python-pygments          \
        python-recommonmark      \
        python-sphinx            \
        rapidjson-dev            \
        time                     \
        unzip                    \
        wget                     \
        zlib1g-dev

ADD deps/k/haskell-backend/src/main/native/haskell-backend/scripts/install-stack.sh /.install-stack/
RUN /.install-stack/install-stack.sh

RUN    git clone 'https://github.com/z3prover/z3' --branch=z3-4.6.0 \
    && cd z3                                                        \
    && python scripts/mk_make.py                                    \
    && cd build                                                     \
    && make -j8                                                     \
    && make install                                                 \
    && cd ../..                                                     \
    && rm -rf z3

RUN curl -sL https://deb.nodesource.com/setup_10.x | bash -
RUN apt-get install --yes nodejs
RUN npm install -g npx

USER user:user

ADD deps/k/k-distribution/src/main/scripts/bin/k-configure-opam-dev deps/k/k-distribution/src/main/scripts/bin/k-configure-opam-common /home/user/.tmp-opam/bin/
ADD deps/k/k-distribution/src/main/scripts/lib/opam  /home/user/.tmp-opam/lib/opam/
RUN    cd /home/user \
    && ./.tmp-opam/bin/k-configure-opam-dev

ENV LC_ALL=C.UTF-8
ADD --chown=user:user deps/k/haskell-backend/src/main/native/haskell-backend/stack.yaml /home/user/.tmp-haskell/
ADD --chown=user:user deps/k/haskell-backend/src/main/native/haskell-backend/kore/package.yaml /home/user/.tmp-haskell/kore/
RUN    cd /home/user/.tmp-haskell \
    && stack build --only-snapshot

ADD deps/k/pom.xml /home/user/.tmp-maven/
ADD deps/k/ktree/pom.xml /home/user/.tmp-maven/ktree/
ADD deps/k/llvm-backend/pom.xml /home/user/.tmp-maven/llvm-backend/
ADD deps/k/llvm-backend/src/main/native/llvm-backend/matching/pom.xml /home/user/.tmp-maven/llvm-backend/src/main/native/llvm-backend/matching/
ADD deps/k/haskell-backend/pom.xml /home/user/.tmp-maven/haskell-backend/
ADD deps/k/ocaml-backend/pom.xml /home/user/.tmp-maven/ocaml-backend/
ADD deps/k/kernel/pom.xml /home/user/.tmp-maven/kernel/
ADD deps/k/java-backend/pom.xml /home/user/.tmp-maven/java-backend/
ADD deps/k/k-distribution/pom.xml /home/user/.tmp-maven/k-distribution/
ADD deps/k/kore/pom.xml /home/user/.tmp-maven/kore/
RUN    cd /home/user/.tmp-maven \
    && mvn dependency:go-offline

ENV LD_LIBRARY_PATH=/usr/local/lib
ENV PATH=/home/user/.local/bin:$PATH
