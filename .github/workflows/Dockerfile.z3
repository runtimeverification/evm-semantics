ARG BASE_IMAGE=ubuntu:jammy
FROM ${BASE_IMAGE}

RUN    apt-get update        \
    && apt-get upgrade --yes \
    && apt-get install --yes \
            clang            \
            cmake            \
            git              \
            python3

RUN    git clone 'https://github.com/z3prover/z3' --branch=z3-4.8.15 \
    && cd z3                                                         \
    && python3 scripts/mk_make.py                                    \
    && cd build                                                      \
    && make -j8                                                      \
    && make install                                                  \
    && cd ../..                                                      \
    && rm -rf z3
