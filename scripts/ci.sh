#!/bin/sh

set -e
set -u

export TOP=${TOP:-$(git rev-parse --show-toplevel)}

$TOP/scripts/check.sh
$TOP/scripts/build.sh
$TOP/scripts/ktest.sh
