FROM runtimeverificationinc/ubuntu:bionic

RUN    apt-get update                \
    && apt-get upgrade --yes         \
    && apt-get install --yes         \
            autoconf                 \
            bison                    \
            clang-8                  \
            cmake                    \
            curl                     \
            flex                     \
            gcc                      \
            jq                       \
            libboost-test-dev        \
            libcrypto++-dev          \
            libffi-dev               \
            libgflags-dev            \
            libjemalloc-dev          \
            libmpfr-dev              \
            libprocps-dev            \
            libsecp256k1-dev         \
            libssl-dev               \
            libtool                  \
            libyaml-dev              \
            lld-8                    \
            llvm-8-tools             \
            make                     \
            maven                    \
            netcat-openbsd           \
            openjdk-11-jdk           \
            pandoc                   \
            pkg-config               \
            python3                  \
            python-pygments          \
            python-recommonmark      \
            python-sphinx            \
            rapidjson-dev            \
            time                     \
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

USER user:user

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
