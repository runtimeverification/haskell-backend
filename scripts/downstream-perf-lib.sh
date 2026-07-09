#!/usr/bin/env bash

downstream_perf_normalize_feature_branch() {
    local raw_branch=$1
    raw_branch=${raw_branch//\//-}
    if [[ $raw_branch == "master" ]]; then
        raw_branch="feature"
    fi
    printf '%s\n' "$raw_branch"
}

downstream_perf_write_kv() {
    local manifest=$1
    local key=$2
    local value=$3
    printf '%s=%q\n' "$key" "$value" >> "$manifest"
}

downstream_perf_write_manifest_snapshot() {
    local manifest=${1:-}
    if [[ -z $manifest ]]; then
        return 0
    fi

    mkdir -p "$(dirname "$manifest")"
    : > "$manifest"

    downstream_perf_write_kv "$manifest" "SUITE" "${DOWNSTREAM_PERF_SUITE-}"
    downstream_perf_write_kv "$manifest" "FEATURE_BRANCH_NAME" "${FEATURE_BRANCH_NAME-}"
    downstream_perf_write_kv "$manifest" "HEAD_COMMIT" "${HEAD_COMMIT-}"
    downstream_perf_write_kv "$manifest" "BASELINE_COMMIT" "${BASELINE_COMMIT-}"
    downstream_perf_write_kv "$manifest" "BASELINE_COMMIT_SHORT" "${BASELINE_COMMIT_SHORT-}"
    downstream_perf_write_kv "$manifest" "FEATURE_LOG" "${FEATURE_LOG-}"
    downstream_perf_write_kv "$manifest" "BASELINE_LOG" "${BASELINE_LOG-}"
    downstream_perf_write_kv "$manifest" "COMPARE_FILE" "${COMPARE_FILE-}"
    downstream_perf_write_kv "$manifest" "FEATURE_STATUS" "${FEATURE_STATUS-unknown}"
    downstream_perf_write_kv "$manifest" "BASELINE_STATUS" "${BASELINE_STATUS-not-run}"
    downstream_perf_write_kv "$manifest" "FEATURE_DURATION_SECONDS" "${FEATURE_DURATION_SECONDS-}"
    downstream_perf_write_kv "$manifest" "BASELINE_DURATION_SECONDS" "${BASELINE_DURATION_SECONDS-}"
    downstream_perf_write_kv "$manifest" "TIMEOUT_SECONDS" "${TIMEOUT_SECONDS-}"
    downstream_perf_write_kv "$manifest" "COMPARE_STATUS" "${COMPARE_STATUS-not-run}"
    downstream_perf_write_kv "$manifest" "SKIP_REASON" "${SKIP_REASON-}"
}

downstream_perf_baseline_commit() {
    local baseline_ref=$1
    git rev-parse "$baseline_ref"
}

downstream_perf_run_and_log() {
    local logfile=$1
    shift

    local start_time end_time status
    start_time=$(date +%s)

    set +e
    # Keep stdout reserved for machine-readable "status duration" output.
    # Stream command output to the console via stderr while preserving a full log file.
    "$@" 2>&1 | tee "$logfile" >&2
    status=${PIPESTATUS[0]}
    set -e

    end_time=$(date +%s)
    printf '%s %s\n' "$status" "$((end_time - start_time))"
}
