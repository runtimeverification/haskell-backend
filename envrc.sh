# Template .envrc for direnv (https://github.com/direnv/direnv)
#
# Set up shell and editors to use the same versions of Haskell and
# K Framework tools used by this project
#
# Usage:
#   1. Install direnv (refer to direnv's documentation).
#   2. Copy this file to .envrc: cp envrc.sh .envrc
#   3. Edit .envrc if required for your environment.
#   4. Load with direnv: direnv allow

export KORE="${KORE:-$(pwd)}"
export K_RELEASE="${K_RELEASE:-$KORE/.build/k}"
export PATH="$KORE/.build/kore/bin:$K_RELEASE/bin:$(stack path --bin-path):$PATH"
