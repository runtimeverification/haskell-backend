#!/usr/bin/env bash

set_results() {
    last_result="result-$(printf "%04d" $last).kore"
    next_result="result-$(printf "%04d" $next).kore"
    echo $last_result $next_result
}

(( next = 0 ))
last_result="input.kore"
next_result="result-0000.kore"
while ! [[ -f $next_result ]] || ! diff "$last_result" "$next_result" >/dev/null
do
    kore-exec $@ --pattern "$last_result" --output "$next_result" --depth 1
    (( last = next ))
    (( next += 1 ))
    set_results
done