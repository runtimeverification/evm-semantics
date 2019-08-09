FROM runtimeverificationinc/ubuntu:bionic

RUN    apt-get update  -q                                                     \
    && apt-get install --yes                                                  \
        autoconf bison clang-8 cmake curl flex gcc libboost-test-dev          \
        libcrypto++-dev libffi-dev libjemalloc-dev libmpfr-dev libprocps-dev  \
        libprotobuf-dev libsecp256k1-dev libssl-dev libtool libyaml-dev lld-8 \
        llvm-8-tools make maven opam openjdk-11-jdk pandoc pkg-config         \
        protobuf-compiler python3 python-pygments python-recommonmark         \
        python-sphinx time zlib1g-dev

USER user:user

# Copy OCaml.
COPY --chown=user:user \
     --from=runtimeverificationinc/ocaml:ubuntu-bionic \
     /home/user/.opam \
     /home/user/.opam

# Copy haskell.
COPY --from=runtimeverificationinc/haskell:ubuntu-bionic \
     --chown=user:user \
     /home/user/.stack \
     /home/user/.stack

COPY --from=runtimeverificationinc/haskell:ubuntu-bionic \
     --chown=user:user \
     /usr/local/bin/stack \
     /usr/local/bin/stack

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
