#!/usr/bin/env bash

set -exuo pipefail

make -j8 -C "${TOP:?}/src/main/k/evm-semantics" test
