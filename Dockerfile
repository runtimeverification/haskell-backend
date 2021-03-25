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

ENV LC_ALL=C.UTF-8

ARG USER_ID=1000
ARG GROUP_ID=1000
RUN    groupadd --gid $GROUP_ID user                                        \
    && useradd --create-home --uid $USER_ID --shell /bin/sh --gid user user

ARG STACK=2.5.1
RUN curl -sSL https://raw.githubusercontent.com/commercialhaskell/stack/v$STACK/etc/scripts/get-stack.sh | sh

USER $USER_ID:$GROUP_ID
WORKDIR /home/user

ADD --chown=user:user stack.yaml .tmp-haskell/
ADD --chown=user:user kore/package.yaml .tmp-haskell/kore/
RUN cd .tmp-haskell && stack build --only-snapshot --test --bench --haddock

RUN mkdir -p /home/user/.ssh
ADD --chown=user:user docker/ssh/config /home/user/.ssh/
RUN    chmod go-rwx -R /home/user/.ssh                                \
    && git config --global user.email "admin@runtimeverification.com" \
    && git config --global user.name  "RV Jenkins"
