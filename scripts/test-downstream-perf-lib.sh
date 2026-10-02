#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(dirname "$(readlink -f "$0")")"
. "$SCRIPT_DIR/downstream-perf-lib.sh"

TEMPD=$(mktemp -d)
trap 'rm -rf "$TEMPD"' EXIT

LOGFILE="$TEMPD/helper.log"

read -r status duration < <(
    downstream_perf_run_and_log \
        "$LOGFILE" \
        bash -c "echo 'feature output line 1'; echo 'feature output line 2'; echo 'feature warning' >&2; exit 7"
)

if [[ $status != "7" ]]; then
    echo "Expected status 7, got '$status'" >&2
    exit 1
fi

if [[ ! $duration =~ ^[0-9]+$ ]]; then
    echo "Expected numeric duration, got '$duration'" >&2
    exit 1
fi

if [[ ! -s $LOGFILE ]]; then
    echo "Expected non-empty logfile at '$LOGFILE'" >&2
    exit 1
fi

grep -q "feature output line 1" "$LOGFILE"
grep -q "feature output line 2" "$LOGFILE"
grep -q "feature warning" "$LOGFILE"
