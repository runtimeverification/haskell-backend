ARG K_COMMIT
FROM runtimeverificationinc/kframework-k:ubuntu-bionic-${K_COMMIT}

ENV TZ=America/Chicago
RUN    ln --symbolic --no-dereference --force /usr/share/zoneinfo/$TZ /etc/localtime \
    && echo $TZ > /etc/timezone

RUN    apt update              \
    && apt upgrade --yes       \
    && apt install --yes       \
           libtinfo-dev        \
           curl git make unzip

ARG STACK=2.5.1
RUN curl -sSL https://raw.githubusercontent.com/commercialhaskell/stack/v$STACK/etc/scripts/get-stack.sh | sh

ARG HUB=2.14.2
RUN    curl -sSL https://github.com/github/hub/releases/download/v$HUB/hub-linux-amd64-$HUB.tgz | tar -xz \
    && ( cd hub-linux-amd64-$HUB && ./install prefix=/usr/local ) \
    && rm -fr hub-linux-amd64-$HUB

ENV LC_ALL=C.UTF-8
ADD ./src/main/kore/prelude.kore /usr/include/kframework/kore/prelude.kore

ARG USER_ID=1000
ARG GROUP_ID=1000
RUN    groupadd --gid $GROUP_ID user                                        \
    && useradd --create-home --uid $USER_ID --shell /bin/sh --gid user user

USER $USER_ID:$GROUP_ID
WORKDIR /home/user

ADD --chown=user:user stack.yaml .tmp-haskell/
ADD --chown=user:user kore/kore.cabal .tmp-haskell/kore/
RUN    ( cd .tmp-haskell && stack build --only-snapshot --test --bench --haddock ) \
    && rm -fr .tmp-haskell

ADD --chown=user:user docker/ssh/config .ssh/
RUN    git config --global user.email "admin@runtimeverification.com" \
    && git config --global user.name  "RV Jenkins"
