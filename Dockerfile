FROM runtimeverificationinc/ubuntu:bionic

RUN    apt-get update  -q                                                     \
    && apt-get upgrade --yes                                                  \
    && apt-get install --yes                                                  \
        autoconf bison clang-8 cmake curl flex gcc libboost-test-dev          \
        libcrypto++-dev libffi-dev libjemalloc-dev libmpfr-dev libprocps-dev  \
        libprotobuf-dev libsecp256k1-dev libssl-dev libtool libyaml-dev lld-8 \
        llvm-8-tools make maven opam openjdk-11-jdk pandoc pkg-config         \
        protobuf-compiler python3 python-pygments python-recommonmark         \
        python-sphinx time zlib1g-dev

COPY deps/k/haskell-backend/src/main/native/haskell-backend/scripts/install-stack.sh /.install-stack/
RUN /.install-stack/install-stack.sh

USER user:user

COPY deps/k/k-distribution/src/main/scripts/bin/k-configure-opam-dev deps/k/k-distribution/src/main/scripts/bin/k-configure-opam-common /home/user/.tmp-opam/bin/
COPY deps/k/k-distribution/src/main/scripts/lib/opam  /home/user/.tmp-opam/lib/opam/
RUN    cd /home/user \
    && ./.tmp-opam/bin/k-configure-opam-dev

COPY --chown=user:user deps/k/haskell-backend/src/main/native/haskell-backend/stack.yaml /home/user/.tmp-haskell/
COPY --chown=user:user deps/k/haskell-backend/src/main/native/haskell-backend/kore/package.yaml /home/user/.tmp-haskell/kore/
RUN    cd /home/user/.tmp-haskell \
    && stack build --only-snapshot

# Copy z3.
COPY --from=runtimeverificationinc/z3:4.6.0-llvm-8-ubuntu-bionic \
     --chown=user:user \
     /z3 /home/user/z3

# Install z3.
RUN    cd /home/user/z3/build \
    && sudo make install      \
    && cd ../..               \
    && rm -rf z3

# Copy rust's .cargo, .rustup, and build-in-source directories.
COPY --chown=user:user \
     --from=runtimeverificationinc/rust:1.34.0-llvm-8-ubuntu-bionic \
     /root/.cargo \
     /home/user/.cargo

COPY --chown=user:user \
     --from=runtimeverificationinc/rust:1.34.0-llvm-8-ubuntu-bionic \
     /root/.rustup \
     /home/user/.rustup

COPY --chown=user:user \
     --from=runtimeverificationinc/rust:1.34.0-llvm-8-ubuntu-bionic \
     /rustc-1.34.0-src \
     /home/user/rustc-1.34.0-src

# Use rustup.
RUN    cd /home/user/rustc-1.34.0-src \
    && /home/user/.cargo/bin/rustup \
         toolchain \
         link \
         rust-1.34.0-llvm-8 \
         build/x86_64-unknown-linux-gnu/stage2
    

# Environment variables.
ENV LD_LIBRARY_PATH=/usr/local/lib
ENV PATH=/home/user/.local/bin:/home/user/.cargo/bin:$PATH
