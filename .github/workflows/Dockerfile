ARG Z3_VERSION
ARG K_VERSION
ARG LLVM_VERSION

ARG Z3_VERSION
FROM runtimeverificationinc/z3:ubuntu-jammy-${Z3_VERSION} AS z3

ARG K_VERSION
FROM runtimeverificationinc/kframework-k:ubuntu-jammy-${K_VERSION}

COPY --from=z3 /usr/bin/z3 /usr/bin/z3

ARG LLVM_VERSION

RUN    apt-get update                  \
    && apt-get upgrade --yes           \
    && apt-get install --yes           \
            clang-${LLVM_VERSION}      \
            cmake                      \
            curl                       \
            debhelper                  \
            libboost-test-dev          \
            libcrypto++-dev            \
            libsecp256k1-dev           \
            libssl-dev                 \
            libyaml-dev                \
            llvm-${LLVM_VERSION}-dev   \
            llvm-${LLVM_VERSION}-tools \
            maven                      \
            openjdk-17-jdk-headless    \
            python3                    \
            python3-pip

# The K frontend (k-frontend jar) of the K commit in deps/k_frontend_rev replaces the one of the K
# release above. Only the Java frontend differs from the release; everything else is unchanged.
ARG K_FRONTEND_REV
RUN    curl -fsSL "https://github.com/runtimeverification/k/archive/${K_FRONTEND_REV}.tar.gz" | tar -xz -C /tmp \
    && cd "/tmp/k-${K_FRONTEND_REV}"                                                                       \
    && mvn --batch-mode --quiet -f k-frontend/pom.xml package -DskipTests                                \
    && jars=$(find / -xdev -path '*/kframework/java/k-frontend-1.0-SNAPSHOT.jar' -not -path '/tmp/*')     \
    && test -n "${jars}"                                                                                  \
    && for jar in ${jars}; do cp -v k-frontend/target/k-frontend-1.0-SNAPSHOT.jar "${jar}"; done          \
    && cd /                                                                                               \
    && rm -rf "/tmp/k-${K_FRONTEND_REV}" /root/.m2

ARG IMAGE_USER=user
ARG IMAGE_GROUP
ARG USER_ID
ARG GROUP_ID
RUN groupadd -g ${GROUP_ID} ${IMAGE_GROUP} && useradd -m -u ${USER_ID} -s /bin/sh -g ${IMAGE_GROUP} ${IMAGE_USER}

USER ${IMAGE_USER}:${IMAGE_GROUP}
RUN mkdir /home/${IMAGE_USER}/workspace
WORKDIR /home/${IMAGE_USER}/workspace

ENV PATH=/home/${IMAGE_USER}/.local/bin:${PATH}

ARG UV_VERSION
RUN    curl -LsSf https://astral.sh/uv/${UV_VERSION}/install.sh | sh \
    && uv --version
