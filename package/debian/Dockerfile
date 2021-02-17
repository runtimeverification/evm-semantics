FROM ubuntu:bionic

ENV TZ America/Chicago
ENV DEBIAN_FRONTEND=noninteractive

RUN    apt-get update        \
    && apt-get upgrade --yes \
    && apt-get install --yes \
                sudo

ARG KEVM_VERSION=1.0.0
COPY kevm_${KEVM_VERSION}_amd64.deb /kevm_${KEVM_VERSION}_amd64.deb
RUN    apt-get update                                        \
    && apt-get upgrade --yes                                 \
    && apt-get install --yes /kevm_${KEVM_VERSION}_amd64.deb \
    && rm -rf /kevm_${KEVM_VERSION}_amd64.deb

ARG USER_ID=1000
ARG GROUP_ID=1000
RUN    groupadd -g $GROUP_ID user                     \
    && useradd -m -u $USER_ID -s /bin/sh -g user user

USER $USER_ID:$GROUP_ID
WORKDIR /home/user
