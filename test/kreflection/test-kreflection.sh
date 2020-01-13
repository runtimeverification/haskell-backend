TOP=$(git rev-parse --show-toplevel)
KRUN=$TOP/.build/k/bin/krun
#echo $KRUN
KORE_EXEC=$TOP/.build/kore/bin/kore-exec
KRUN_OPTS="--haskell-backend-command \"$KORE_EXEC --disable-log-timestamps\""
#echo $KRUN_OPTS
COMMAND="$KRUN $KRUN_OPTS -d . 1.kreflection 2>test-kreflection.sh.out || true"
eval $COMMAND