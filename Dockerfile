FROM ubuntu:bionic

ENV TZ=America/Chicago
RUN    ln --symbolic --no-dereference --force /usr/share/zoneinfo/$TZ /etc/localtime \
    && echo $TZ > /etc/timezone

RUN apt update && apt upgrade --yes

RUN apt install --yes                                                        \
        autoconf bison build-essential clang++-6.0 clang-6.0 cmake coreutils \
        curl diffutils flex gcc git gnupg jq libboost-test-dev libffi-dev    \
        libgmp-dev libjemalloc-dev libmpfr-dev libstdc++6 libtool libxml2    \
        libyaml-cpp-dev llvm-6.0 m4 make maven opam openjdk-8-jdk pandoc     \
        pkg-config python3 python-jinja2 python-pygments python-recommonmark \
        scala stylish-haskell time libtinfo-dev unifdef zlib1g-dev

RUN update-alternatives --set java /usr/lib/jvm/java-8-openjdk-amd64/jre/bin/java

RUN curl -sSL https://get.haskellstack.org/ | sh

RUN    git clone 'https://github.com/z3prover/z3' --branch=z3-4.8.4 \
    && cd z3                                                        \
    && python scripts/mk_make.py                                    \
    && cd build                                                     \
    && make -j8                                                     \
    && make install                                                 \
    && cd ../..                                                     \
    && rm -rf z3

ARG USER_ID=1000
ARG GROUP_ID=1000
RUN    groupadd --gid $GROUP_ID user                                        \
    && useradd --create-home --uid $USER_ID --shell /bin/sh --gid user user

USER $USER_ID:$GROUP_ID

RUN curl https://sh.rustup.rs -sSf | sh -s -- -y --default-toolchain 1.28.0

RUN    cd /home/user                                                          \
    && git clone 'https://github.com/kframework/k' --branch=nightly-0f3835d3a \
    && ./k/k-distribution/src/main/scripts/bin/k-configure-opam-dev           \
    && rm -rf k

ADD --chown=user:user stack.yaml /home/user/.tmp-haskell/
ADD --chown=user:user src/main/haskell/kore/package.yaml /home/user/.tmp-haskell/src/main/haskell/kore/
RUN    cd /home/user/.tmp-haskell \
    && stack build --only-dependencies --test --bench --haddock --library-profiling
