#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(dirname "$(readlink -f "$0")")"
. "$SCRIPT_DIR/downstream-perf-lib.sh"

SUITE=$1
MANIFEST_PATH=$2
REASON=$3
RAW_FEATURE_BRANCH=$4

if [[ -f $MANIFEST_PATH ]]; then
    # shellcheck disable=SC1090
    . "$MANIFEST_PATH"
fi

FEATURE_BRANCH_NAME=${FEATURE_BRANCH_NAME:-"$(downstream_perf_normalize_feature_branch "$RAW_FEATURE_BRANCH")"}
OUTPUT_DIR="downstream-perf/$SUITE"
SUMMARY_FILE="$OUTPUT_DIR/summary.md"
TITLE="KEVM downstream performance"
if [[ $SUITE == "kontrol" ]]; then
    TITLE="Kontrol downstream performance"
fi

mkdir -p "$OUTPUT_DIR"

if [[ -f $MANIFEST_PATH ]]; then
    cp "$MANIFEST_PATH" "$OUTPUT_DIR/manifest.env"
fi

copy_if_present() {
    local maybe_path=$1
    if [[ -n $maybe_path && -f $maybe_path ]]; then
        cp "$maybe_path" "$OUTPUT_DIR/"
    fi
}

copy_if_present "${FEATURE_LOG:-}"
copy_if_present "${BASELINE_LOG:-}"
copy_if_present "${COMPARE_FILE:-}"

{
    echo "## $TITLE"
    echo
    echo "- Trigger: $REASON"
    echo "- Feature branch: $FEATURE_BRANCH_NAME"
    if [[ -n ${HEAD_COMMIT:-} ]]; then
        echo "- Head commit: $HEAD_COMMIT"
    fi
    if [[ -n ${BASELINE_COMMIT_SHORT:-} ]]; then
        echo "- Baseline commit: $BASELINE_COMMIT_SHORT"
    fi
    echo "- Feature status: ${FEATURE_STATUS:-unknown}"
    if [[ -n ${FEATURE_DURATION_SECONDS:-} ]]; then
        echo "- Feature duration (seconds): $FEATURE_DURATION_SECONDS"
    fi
    if [[ ${BASELINE_STATUS:-not-run} != "not-run" ]]; then
        echo "- Baseline status: $BASELINE_STATUS"
    fi
    if [[ -n ${BASELINE_DURATION_SECONDS:-} ]]; then
        echo "- Baseline duration (seconds): $BASELINE_DURATION_SECONDS"
    fi
    if [[ -n ${SKIP_REASON:-} ]]; then
        echo "- Skip reason: $SKIP_REASON"
    fi
    echo

    if [[ -f ${COMPARE_FILE:-} ]]; then
        echo "- Compare file: $(basename "$COMPARE_FILE")"
        echo
        if [[ -s $COMPARE_FILE ]]; then
            cat "$COMPARE_FILE"
        else
            echo "No significant performance deltas above the current compare thresholds."
        fi
    elif [[ ${FEATURE_STATUS:-unknown} == "budget-exceeded" && ${BASELINE_STATUS:-not-run} == "budget-exceeded" ]]; then
        echo "Feature and baseline runs both exceeded the configured budget, so compare output is unavailable."
    elif [[ ${FEATURE_STATUS:-unknown} == "budget-exceeded" ]]; then
        echo "Feature run exceeded the configured budget, so baseline comparison was skipped."
    elif [[ ${FEATURE_STATUS:-unknown} != "success" ]]; then
        echo "Feature run failed before a compare artifact could be produced."
    elif [[ ${BASELINE_STATUS:-not-run} != "success" ]]; then
        echo "Baseline run did not complete, so compare output is unavailable."
    else
        echo "No compare artifact was produced."
    fi
} | tee "$SUMMARY_FILE" >> "$GITHUB_STEP_SUMMARY"
