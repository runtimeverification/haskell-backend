#!/usr/bin/env bash

set -exuo pipefail

make -j8 -C "${KEVM_DIR:?}" \
    TEST_CONCRETE_BACKEND=haskell TEST_SYMBOLIC_BACKEND=haskell \
    test-interactive-run test-interactive-search
