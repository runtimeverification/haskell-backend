#!/bin/sh

#IGNORE=$($KORE_REPL sum-spec-vdefinition.kore -r --repl-script run-stepf-repl-script-spec.k.repl --module VERIFICATION --prove sum-spec.kore --spec-module SUM-SPEC)
IGNORE=$($KPROVE --haskell-backend-command $KORE_REPL -d . -m VERIFICATION sum-spec.k)

if grep -q "Config at node 10" shouldBeAt10.out; then
    if grep -q "Config at node 18" shouldBeAt18.out; then
        diff finished.out finished.out.golden
    else
        echo "Current node is not equal to expected value 10 after second call to stepf."
    fi
else
    echo "Current node is not equal to expected value 18 after first call to stepf."
fi

rm shouldBeAt10.out
rm shouldBeAt18.out
rm finished.out
