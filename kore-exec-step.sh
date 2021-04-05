#!/usr/bin/env bash

set_results() {
    last_result="result-$(printf "%04d" $last).kore"
    next_result="result-$(printf "%04d" $next).kore"
}

kore_exec_args=()
while [[ $# -gt 0 ]]
do
    case "$1" in
        --pattern)
            last_result="$2"
            shift
            ;;
        *)
            kore_exec_args+=("$1")
    esac
    shift
done

(( next = 0 ))
next_result="result-0000.kore"
while ! [[ -f $next_result ]] || ! diff "$last_result" "$next_result" >/dev/null
do
    command time -f '%S,%U,%M' -o "kore-exec-time.csv" -a -q \
        kore-exec "${kore_exec_args[@]}" \
            --pattern "${last_result:?}" --output "${next_result:?}" --depth 1
    (( last = next ))
    (( next += 1 ))
    set_results
done