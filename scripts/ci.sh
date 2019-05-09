#!/usr/bin/env bash

set -exuo pipefail

export TOP=${TOP:-$(git rev-parse --show-toplevel)}

$TOP/scripts/check.sh
$TOP/scripts/lint.sh
$TOP/scripts/build.sh
$TOP/scripts/ktest.sh
