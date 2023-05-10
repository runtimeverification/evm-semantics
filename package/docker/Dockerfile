FROM ghcr.io/foundry-rs/foundry:nightly-aeba75e4799f1e11e3daba98d967b83e286b0c4a as FOUNDRY

FROM ubuntu:jammy

ENV TZ=America/Chicago
ENV DEBIAN_FRONTEND=noninteractive

COPY --from=FOUNDRY /usr/local/bin/forge /usr/local/bin/forge
COPY --from=FOUNDRY /usr/local/bin/anvil /usr/local/bin/anvil
COPY --from=FOUNDRY /usr/local/bin/cast /usr/local/bin/cast

RUN    apt-get update        \
    && apt-get upgrade --yes \
    && apt-get install --yes \
        curl                 \
        git                  \
        make                 \
        python3              \
        python3-pip          \
        sudo                 \
        wget

RUN echo '%sudo ALL=(ALL) NOPASSWD:ALL' >> /etc/sudoers

RUN curl -sSL https://install.python-poetry.org | POETRY_HOME=/usr python3 - --version 1.3.2

ARG USER_ID=1000
ARG GROUP_ID=1000
RUN    groupadd -g $GROUP_ID user                             \
    && useradd -m -u $USER_ID -s /bin/sh -g user user -G sudo

USER $USER_ID:$GROUP_ID
WORKDIR /home/user

ARG K_VERSION
RUN wget https://github.com/runtimeverification/k/releases/download/v${K_VERSION}/kframework_${K_VERSION}_amd64_ubuntu_jammy.deb
RUN    sudo apt-get update        \
    && sudo apt-get upgrade --yes \
    && sudo apt-get install --yes ./kframework_${K_VERSION}_amd64_ubuntu_jammy.deb

ARG KEVM_VERSION
ADD --chown=user:user ./kevm_${KEVM_VERSION}_amd64.deb ./
RUN    sudo apt-get update        \
    && sudo apt-get upgrade --yes \
    && sudo apt-get install --yes ./kevm_${KEVM_VERSION}_amd64.deb

ADD --chown=user:user ./kevm-pyk /home/user/kevm-pyk
RUN cd /home/user/kevm-pyk && pip3 install .
