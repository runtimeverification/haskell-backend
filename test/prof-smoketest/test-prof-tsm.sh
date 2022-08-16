#! /bin/sh

tar -O -xzf example.eventlog.tgz > test-prof-tsm-eventlog && \
    ${KORE_PROF:?} \
        --timing-state-machine Unify \
        -o test-prof-tsm.sh.tmp \
        test-prof-tsm-eventlog  \
            > /dev/null && \
    rm test-prof-tsm-eventlog && \
    cat test-prof-tsm.sh.tmp
