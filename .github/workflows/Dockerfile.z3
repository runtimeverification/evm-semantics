FROM ubuntu:jammy

ENV TZ=America/Chicago
RUN ln -snf /usr/share/zoneinfo/$TZ /etc/localtime && echo $TZ > /etc/timezone

RUN    apt-get update        \
    && apt-get upgrade --yes \
    && apt-get install --yes \
            clang            \
            cmake            \
            git              \
            python3

ARG Z3_VERSION=4.12.1
RUN    git clone 'https://github.com/z3prover/z3' --branch=z3-${Z3_VERSION} \
    && cd z3                                                                \
    && python3 scripts/mk_make.py                                           \
    && cd build                                                             \
    && make -j8                                                             \
    && make install                                                         \
    && cd ../..                                                             \
    && rm -rf z3
