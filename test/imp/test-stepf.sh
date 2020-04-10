#!/bin/sh

#IGNORE=$($KPROVE --haskell-backend-command "$KORE_REPL -r --repl-script run-stepf-repl-script-spec.k.repl" -d . -m VERIFICATION sum-spec.k)
IGNORE=$(make sum-spec.k.run-repl-script)

if grep -q "Config at node 10" shouldBeAt10.out; then
    if grep -q "Config at node 18" shouldBeAt18.out; then
        cat finished.out
    else
        echo "Current node is not equal to expected value 18 after second call to stepf."
    fi
else
    echo "Current node is not equal to expected value 10 after first call to stepf."
fi

rm shouldBeAt10.out shouldBeAt18.out
