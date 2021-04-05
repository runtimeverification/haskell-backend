#!/usr/bin/env bash

set_results() {
    last_result="result-$(printf "%04d" $last).kore"
    next_result="result-$(printf "%04d" $next).kore"
}
(( last = 0 ))
(( next = 1 ))
set_results

kore_exec_args=()
while [[ $# -gt 0 ]]
do
    case "$1" in
        --pattern)
            pattern="$2"
            shift
            ;;
        --output)
            shift
            ;;
        --depth)
            depth="$2"
            shift
            ;;
        *)
            kore_exec_args+=("$1")
    esac
    shift
done

if [[ -z "$pattern" ]]
then
    echo >&2 "Error: Missing --pattern FILENAME argument"
    exit 1
fi
last_result="$pattern"
trap 'exit 1' SIGINT

while [[ -z "$depth" ]] || [[ "$last" -lt "$depth" ]]
do
    command time -f '%S,%U,%M' -o "kore-exec-time.csv" -a -q \
        kore-exec "${kore_exec_args[@]}" \
            --pattern "${last_result:?}" --output "${next_result:?}" --depth 1
    if diff "$last_result" "$next_result" >/dev/null; then break; fi
    (( last = next ))
    (( next += 1 ))
    set_results
done
