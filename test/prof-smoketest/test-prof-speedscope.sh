#! /bin/sh
tar -O -xzf example.eventlog.tgz > test-prof-speedscope-eventlog && \
    ${KORE_PROF:?} test-prof-speedscope-eventlog && \
    rm test-prof-speedscope-eventlog
