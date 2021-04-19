ARG K_COMMIT
FROM runtimeverificationinc/kframework-k:ubuntu-bionic-${K_COMMIT}

ENV TZ=America/Chicago
RUN    ln --symbolic --no-dereference --force /usr/share/zoneinfo/$TZ /etc/localtime \
    && echo $TZ > /etc/timezone

RUN    apt update                                                                \
    && apt upgrade --yes                                                         \
    && apt install --yes                                                         \
           libtinfo-dev                                                          \
           curl git make unzip

ENV LC_ALL=C.UTF-8
ADD ./src/main/kore/prelude.kore /usr/include/kframework/kore/prelude.kore

ARG USER_ID=1000
ARG GROUP_ID=1000
RUN    groupadd --gid $GROUP_ID user                                        \
    && useradd --create-home --uid $USER_ID --shell /bin/sh --gid user user

ARG STACK=2.5.1
RUN curl -sSL https://raw.githubusercontent.com/commercialhaskell/stack/v$STACK/etc/scripts/get-stack.sh | sh

USER $USER_ID:$GROUP_ID
WORKDIR /home/user

ADD --chown=user:user stack.yaml .tmp-haskell/
ADD --chown=user:user kore/kore.cabal .tmp-haskell/kore/
RUN cd .tmp-haskell && stack build --only-snapshot --test --bench --haddock
