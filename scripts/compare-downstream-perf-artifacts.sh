#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 4 ]]; then
    echo "Usage: $0 <suite> <master-raw-root> <current-raw-root> <output-dir>" >&2
    exit 2
fi

SUITE=$1
MASTER_RAW_ROOT=$2
CURRENT_RAW_ROOT=$3
OUTPUT_DIR=$4
SCRIPT_DIR="$(dirname "$(readlink -f "$0")")"

mkdir -p "$OUTPUT_DIR"

find_manifest() {
    local root=$1
    find "$root" -type f -name manifest.env | head -n 1
}

MASTER_MANIFEST=$(find_manifest "$MASTER_RAW_ROOT")
CURRENT_MANIFEST=$(find_manifest "$CURRENT_RAW_ROOT")

if [[ -z $MASTER_MANIFEST || -z $CURRENT_MANIFEST ]]; then
    {
        echo "## ${SUITE^^} compare"
        echo
        echo "- Error: missing raw manifest(s)"
        echo "- Master manifest: ${MASTER_MANIFEST:-missing}"
        echo "- Current manifest: ${CURRENT_MANIFEST:-missing}"
    } > "$OUTPUT_DIR/summary.md"
    {
        echo "SUITE=$SUITE"
        echo "MASTER_STATUS=missing"
        echo "CURRENT_STATUS=missing"
        echo "COMPARE_STATUS=missing-input"
    } > "$OUTPUT_DIR/summary.env"
    exit 1
fi

MASTER_DIR=$(dirname "$MASTER_MANIFEST")
CURRENT_DIR=$(dirname "$CURRENT_MANIFEST")

# shellcheck disable=SC1090
. "$MASTER_MANIFEST"
MASTER_STATUS=${FEATURE_STATUS:-unknown}
MASTER_DURATION_SECONDS=${FEATURE_DURATION_SECONDS:-}
MASTER_HEAD_COMMIT=${HEAD_COMMIT:-}

# shellcheck disable=SC1090
. "$CURRENT_MANIFEST"
CURRENT_STATUS=${FEATURE_STATUS:-unknown}
CURRENT_DURATION_SECONDS=${FEATURE_DURATION_SECONDS:-}
CURRENT_HEAD_COMMIT=${HEAD_COMMIT:-}

MASTER_LOG=$(find "$MASTER_DIR" -maxdepth 1 -type f -name '*.log' | head -n 1)
CURRENT_LOG=$(find "$CURRENT_DIR" -maxdepth 1 -type f -name '*.log' | head -n 1)

COMPARE_STATUS=skipped
COMPARE_REASON='compare-skipped'
COMPARE_FILE="$OUTPUT_DIR/compare.txt"

if [[ $MASTER_STATUS == success && $CURRENT_STATUS == success ]]; then
    if [[ -n $MASTER_LOG && -n $CURRENT_LOG ]]; then
        python3 "$SCRIPT_DIR/compare.py" "$CURRENT_LOG" "$MASTER_LOG" > "$COMPARE_FILE"
        COMPARE_STATUS=success
        COMPARE_REASON='ok'
    else
        COMPARE_STATUS=error
        COMPARE_REASON='missing-log-input'
    fi
elif [[ $MASTER_STATUS != success && $CURRENT_STATUS != success ]]; then
    COMPARE_REASON='both-non-success'
else
    COMPARE_REASON='one-side-non-success'
fi

cp -R "$MASTER_DIR" "$OUTPUT_DIR/master"
cp -R "$CURRENT_DIR" "$OUTPUT_DIR/current"

{
    echo "## ${SUITE^^} compare"
    echo
    echo "| Side | Status | Duration (s) | Head commit |"
    echo "| --- | --- | ---: | --- |"
    echo "| master | ${MASTER_STATUS:-unknown} | ${MASTER_DURATION_SECONDS:-n/a} | ${MASTER_HEAD_COMMIT:-n/a} |"
    echo "| current | ${CURRENT_STATUS:-unknown} | ${CURRENT_DURATION_SECONDS:-n/a} | ${CURRENT_HEAD_COMMIT:-n/a} |"
    echo
    if [[ -f $COMPARE_FILE ]]; then
        echo "- Compare file: $(basename "$COMPARE_FILE")"
    else
        echo "- Compare file: not generated"
    fi
} > "$OUTPUT_DIR/summary.md"

{
    echo "SUITE=$SUITE"
    echo "MASTER_STATUS=$MASTER_STATUS"
    echo "MASTER_DURATION_SECONDS=${MASTER_DURATION_SECONDS:-}"
    echo "MASTER_HEAD_COMMIT=${MASTER_HEAD_COMMIT:-}"
    echo "CURRENT_STATUS=$CURRENT_STATUS"
    echo "CURRENT_DURATION_SECONDS=${CURRENT_DURATION_SECONDS:-}"
    echo "CURRENT_HEAD_COMMIT=${CURRENT_HEAD_COMMIT:-}"
    echo "COMPARE_STATUS=$COMPARE_STATUS"
    echo "COMPARE_REASON=$COMPARE_REASON"
} > "$OUTPUT_DIR/summary.env"

if [[ $MASTER_STATUS != success || $CURRENT_STATUS != success ]]; then
    exit 1
fi

if [[ $COMPARE_STATUS != success ]]; then
    exit 1
fi
