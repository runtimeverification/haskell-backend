#!/usr/bin/env bash
set -euo pipefail

# Build and run booster benchmarks with profiling options enabled.
#
# Usage:
#   scripts/run-bench-profile.sh cpu
#   scripts/run-bench-profile.sh heap
#   scripts/run-bench-profile.sh cpu --benchmark-options="--csv benchmarks.csv"
#
# Output artifacts:
#   cpu mode  -> booster-bench.prof
#   heap mode -> booster-bench.hp (and related heap profile outputs)
#
# Build tool: stack is preferred when available; set BENCH_TOOL=cabal (or
# BENCH_TOOL=stack) to force a specific one.

mode="${1:-cpu}"
if [[ $# -gt 0 ]]; then
  shift
fi

benchmark_options=""
for arg in "$@"; do
  case "$arg" in
    --benchmark-options=*)
      benchmark_options="${arg#*=}"
      ;;
    *)
      echo "Unknown argument: $arg" >&2
      echo "Expected: --benchmark-options=..." >&2
      exit 2
      ;;
  esac
done

case "$mode" in
  cpu)
    rts_flags=("-p")
    ;;
  heap)
    rts_flags=("-hc")
    ;;
  *)
    echo "Mode must be one of: cpu, heap" >&2
    exit 2
    ;;
esac

tool="${BENCH_TOOL:-}"
if [[ -z "$tool" ]]; then
  if command -v stack >/dev/null 2>&1; then
    tool=stack
  elif command -v cabal >/dev/null 2>&1; then
    tool=cabal
  else
    echo "Neither stack nor cabal is available in PATH." >&2
    exit 127
  fi
fi

case "$tool" in
  stack)
    bench_args=()
    if [[ -n "$benchmark_options" ]]; then
      bench_args+=("$benchmark_options")
    fi
    bench_args+=(+RTS)
    bench_args+=("${rts_flags[@]}")
    bench_args+=(-RTS)

    cmd=(
      stack bench hs-backend-booster:booster-bench
      --profile
      --ghc-options "-fexternal-interpreter"
      --ba "${bench_args[*]}"
    )
    ;;
  cabal)
    cmd=(cabal bench booster-bench --flags profiling)
    if [[ -n "$benchmark_options" ]]; then
      cmd+=("--benchmark-options=$benchmark_options")
    fi
    cmd+=(-- +RTS)
    cmd+=("${rts_flags[@]}")
    cmd+=(-RTS)
    ;;
  *)
    echo "BENCH_TOOL must be one of: stack, cabal" >&2
    exit 2
    ;;
esac

echo "Running profiling benchmark command:"
printf '  %q' "${cmd[@]}"
printf '\n'
"${cmd[@]}"
