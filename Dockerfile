FROM ubuntu:bionic

ENV TZ=America/Chicago
RUN    ln --symbolic --no-dereference --force /usr/share/zoneinfo/$TZ /etc/localtime \
    && echo $TZ > /etc/timezone

RUN    apt update                                                                \
    && apt upgrade --yes                                                         \
    && apt install --yes                                                         \
           bison curl flex gcc git jq                                            \
           make openjdk-8-jdk pandoc                                             \
           libtinfo-dev                                                          \
           python3 python-pygments python-recommonmark python-sphinx             \
           time unzip wget

RUN update-alternatives --set java /usr/lib/jvm/java-8-openjdk-amd64/jre/bin/java

ARG USER_ID=1000
ARG GROUP_ID=1000
RUN    groupadd --gid $GROUP_ID user                                        \
    && useradd --create-home --uid $USER_ID --shell /bin/sh --gid user user

ADD scripts/install-stack.sh /home/user/.install-stack/
RUN /home/user/.install-stack/install-stack.sh

USER $USER_ID:$GROUP_ID

ENV LC_ALL=C.UTF-8

ARG Z3=4.8.8
RUN    cd /home/user \
    && wget https://github.com/Z3Prover/z3/releases/download/z3-$Z3/z3-$Z3-x64-ubuntu-16.04.zip \
    && unzip z3-$Z3-x64-ubuntu-16.04.zip \
    && rm z3-$Z3-x64-ubuntu-16.04.zip \
    && mv z3-$Z3-x64-ubuntu-16.04 z3
ENV PATH=/home/user/z3/bin:$PATH

ARG HLINT=3.2
RUN    cd /home/user \
    && curl https://github.com/ndmitchell/hlint/releases/download/v$HLINT/hlint-$HLINT-x86_64-linux.tar.gz -sSfL | tar xzf - \
    && mv hlint-$HLINT hlint
ENV PATH=/home/user/hlint:$PATH

ARG STYLISH_HASKELL=0.11.0.0
RUN    cd /home/user \
    && curl https://github.com/jaspervdj/stylish-haskell/releases/download/v$STYLISH_HASKELL/stylish-haskell-v$STYLISH_HASKELL-linux-x86_64.tar.gz -sSfL | tar xzf - \
    && mv stylish-haskell-v$STYLISH_HASKELL-linux-x86_64 stylish-haskell
ENV PATH=/home/user/stylish-haskell:$PATH

ADD --chown=user:user stack.yaml /home/user/.tmp-haskell/
ADD --chown=user:user kore/package.yaml /home/user/.tmp-haskell/kore/
RUN    cd /home/user/.tmp-haskell \
    && stack build --only-snapshot --test --bench --haddock
