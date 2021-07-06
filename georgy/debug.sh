#!/bin/bash

K_FILE=test.k

LOG_FILE=debug.log
LOG_ENTRIES=DebugAttemptEquation,DebugApplyEquation
# LOG_ENTRIES=DebugAppliedRewriteRules,DebugAttemptEquation,DebugApplyEquation
export KORE_EXEC_OPTS="--log ${LOG_FILE} --log-entries ${LOG_ENTRIES}"
# export KORE_EXEC_OPTS="--log ${LOG_FILE} --debug-equation \"LblSet'Coln'difference{}\""

rm -r test-kompiled
rm $LOG_FILE

kompile --backend haskell $K_FILE --main-module TEST --syntax-module TEST
kprove test.k --def-module TEST --spec-module TEST-SPEC
