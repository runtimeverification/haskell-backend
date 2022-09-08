function try() {
    local n
    local tsec
    n=$1
    if [[ $n -le 0 ]]; then
        echo "Repetitions $n <= 0, nothing to do"
        return 0
    fi
    tsec=$2
    if [[ ${tsec} -le 3 ]];
    then echo "Timeout ${tsec} <= 3, too small"
         return 42
    fi
    for i in $(seq 1 $n); do
        if (timeout ${tsec}s stack test);
        then echo "#################### Run $i OK ####################"
        else echo "#################### FAILED IN RUN $i #############"
             return 43
        fi
    done
}
