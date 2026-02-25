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

if command -v cabal >/dev/null 2>&1; then
  cmd=(cabal bench booster-bench --flags profiling)
  if [[ -n "$benchmark_options" ]]; then
    cmd+=("--benchmark-options=$benchmark_options")
  fi
  cmd+=(-- +RTS)
  cmd+=("${rts_flags[@]}")
  cmd+=(-RTS)
elif command -v stack >/dev/null 2>&1; then
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
else
  echo "Neither cabal nor stack is available in PATH." >&2
  exit 127
fi

echo "Running profiling benchmark command:"
printf '  %q' "${cmd[@]}"
printf '\n'
"${cmd[@]}"
