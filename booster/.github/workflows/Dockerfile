ARG BASE_OS
ARG BASE_DISTRO
ARG HPACK_VERSION
ARG GHC_VERSION

FROM haskell:${GHC_VERSION}-buster

ENV TZ America/Chicago
ENV DEBIAN_FRONTEND=noninteractive

ARG HPACK_VERSION
ARG FOURMOLU_VERSION
ARG HLINT_VERSION

RUN    apt-get update        \
    && apt-get install --yes \
        curl                 \
        libsecp256k1-0       \
        libsecp256k1-dev     \
        libtinfo5            \
        locales              \
        git                  \
        z3

RUN locale-gen en_US.UTF-8
ENV LANG en_US.UTF-8
ENV LANGUAGE en_US:en
ENV LC_ALL en_US.UTF-8

# install hpack and hlint from binary packages
RUN    curl -sSL https://github.com/sol/hpack/releases/download/${HPACK_VERSION}/hpack_linux.gz | gunzip -c > /usr/bin/hpack \
    && chmod +x /usr/bin/hpack \
    && hpack --version

# The image is built specifically for an environment with this user/group
ARG USER=github-user
ARG GROUP=$USER
ARG USER_ID=1000
ARG GROUP_ID=$USER_ID
RUN groupadd -g $GROUP_ID $GROUP && useradd -m -u $USER_ID -s /bin/sh -g $GROUP $USER

USER $USER:$GROUP
ENV PATH $PATH:/home/$USER/.cabal/bin

RUN    cd $HOME \
    && cabal update