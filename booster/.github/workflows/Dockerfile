ARG BASE_OS
ARG BASE_DISTRO
ARG HPACK_VERSION
ARG FOURMOLU_VERSION
ARG HLINT_VERSION
ARG GHC_VERSION

FROM haskell:${GHC_VERSION}-slim-buster

ENV TZ America/Chicago
ENV DEBIAN_FRONTEND=noninteractive

ARG HPACK_VERSION
ARG FOURMOLU_VERSION
ARG HLINT_VERSION

RUN    apt-get update        \
    && apt-get install --yes \
        curl                 \
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
RUN curl -sSL https://github.com/ndmitchell/hlint/releases/download/v${HLINT_VERSION}/hlint-${HLINT_VERSION}-x86_64-linux.tar.gz | tar xvz hlint-${HLINT_VERSION}/hlint \
    && mv hlint-${HLINT_VERSION}/hlint /usr/bin/hlint \
    && chmod +x /usr/bin/hlint \
    && hlint --version

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
# install fourmolu from source (binary package not working in this docker image)
RUN    cd $HOME \
    && cabal install fourmolu-${FOURMOLU_VERSION} \
    && fourmolu --version \
