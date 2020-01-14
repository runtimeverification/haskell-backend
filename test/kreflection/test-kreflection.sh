#!/bin/sh
TOP=$(git rev-parse --show-toplevel)
KRUN=$TOP/.build/k/bin/krun
KORE_EXEC=$TOP/.build/kore/bin/kore-exec
KRUN_OPTS="--haskell-backend-command \"$KORE_EXEC --disable-log-timestamps\""
COMMAND="$KRUN $KRUN_OPTS -d . 1.kreflection 2>test-kreflection.sh.out || true"
KOMPILE="$TOP/.build/k/bin/kompile kreflection.k --backend haskell"
eval $KOMPILE
eval $COMMAND